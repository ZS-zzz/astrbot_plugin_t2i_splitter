from astrbot.api.event import filter, AstrMessageEvent, MessageChain
from astrbot.api.star import Context, Star, register
from astrbot.api import logger
from astrbot.api.message_components import Plain, BaseMessageComponent, Reply, Record

import re
import io
import os
import uuid
import time
import math
import asyncio
import threading
import platform
from typing import List, Dict
from datetime import datetime

try:
    from zoneinfo import ZoneInfo
except ImportError:
    ZoneInfo = None

from PIL import Image, ImageDraw, ImageFont, ImageFilter, ImageOps

try:
    import requests
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False

try:
    import psutil
    HAS_PSUTIL = True
except ImportError:
    HAS_PSUTIL = False

# ============ 主题色板 ============
LIGHT_THEME = {
    "bg_start":       (245, 249, 255),
    "bg_end":         (227, 242, 253),
    "text":           (31, 44, 56, 255),
    "text_soft":      (76, 90, 103, 255),
    "primary":        (30, 136, 229, 255),
    "accent":         (66, 165, 245, 255),
    "card_bg":        (255, 255, 255, 80),
    "card_border":    (255, 255, 255, 200),
    "quote_bg":       (30, 136, 229, 20),
    "quote_border":   (30, 136, 229, 80),
    "status_bg":      (30, 136, 229, 15),
    "status_border":  (30, 136, 229, 70),
}

DARK_THEME = {
    "bg_start":       (18, 31, 42),
    "bg_end":         (26, 44, 54),
    "text":           (238, 244, 255, 255),
    "text_soft":      (176, 190, 197, 255),
    "primary":        (100, 181, 246, 255),
    "accent":         (144, 202, 249, 255),
    "card_bg":        (0, 0, 0, 70),
    "card_border":    (255, 255, 255, 60),
    "quote_bg":       (100, 181, 246, 20),
    "quote_border":   (100, 181, 246, 90),
    "status_bg":      (100, 181, 246, 15),
    "status_border":  (100, 181, 246, 80),
}

FALLBACK_QUOTES = [
    "愿你今天的每一分钟，都藏着小惊喜。",
    "慢慢来，比较快。",
    "星光不问赶路人，时光不负有心人。",
    "今天也要元气满满哦！",
    "前方的路还很长，但值得期待。",
    "方寸之间，亦有天地。",
    "把每一天都当成礼物去度过。",
    "心之所向，素履以往。",
    "行动，是治愈恐惧最好的良药。",
    "山高路远，行则将至。",
    "且听风吟，静待花开。",
    "一生温暖纯良，不舍爱与自由。",
]

DEFAULT_BG_URLS = ["https://uapis.cn/api/v1/random/image?category=acg", "https://www.loliapi.com/acg/"]
DEFAULT_QUOTE_APIS = ["https://v1.hitokoto.cn/?c=d&c=i&c=k&encode=json", "https://api.xygeng.cn/one"]


@register(
    "astrbot_plugin_t2i_splitter",
    "无名小服",
    "文本转图片 + 智能分段融合插件 (布局修复 & 极简配置)",
    "v1.3.0",
)
class ForceT2ISplitterPlugin(Star):
    def __init__(self, context: Context, config: dict = None):
        super().__init__(context)
        self.config = config or {}
        self.plugin_dir = os.path.dirname(os.path.abspath(__file__))

        # ---------- 核心自定义配置 ----------
        self.card_width   = self._cfg_int("卡片宽度", 1000)
        self.font_size    = self._cfg_int("字体大小", 28)
        self.theme_mode   = self._cfg_str("主题模式", "自动") # 自动/浅色/深色
        self.brand_name   = self._cfg_str("品牌名称", "无名小服")
        self.show_header  = self._cfg_bool("显示头部", True)
        self.show_quote   = self._cfg_bool("显示每日一言", True)
        self.show_status  = self._cfg_bool("显示服务器状态", True)
        self.status_detail = self._cfg_str("状态详细程度", "简洁") # 简洁/详细
        self.image_render_mode = self._cfg_str("图片转换方式", "多图分段") # 多图分段/单图保留分句
        self.max_segments = self._cfg_int("最大分段数", 5)

        # ---------- 内部硬编码默认值 (无需用户配置) ----------
        self.timezone_str = "Asia/Shanghai"
        self.dark_from = 18
        self.dark_to = 6
        self.bg_urls = DEFAULT_BG_URLS
        self.quote_apis = DEFAULT_QUOTE_APIS
        self.enable_split = True
        self.enable_reply = True
        self.min_segment_length = 10
        self.split_chars = ["。", "？", "！", "?", "!", "；", ";", "\n"]
        self.no_split_around = []
        self.send_speed = "自然" # 快速/自然/慢速
        self.split_scope = "llm_only"
        self.clean_before_items = []
        self.clean_after_items = []

        self.tz = None
        if ZoneInfo:
            try:
                self.tz = ZoneInfo(self.timezone_str)
            except Exception:
                pass

        self._processing_locks: Dict[str, asyncio.Lock] = {}
        self.pair_map = {'"': '"', "《": "》", "（": "）", "(": ")", "[": "]", "{": "}", "'": "'", "【": "】", "<": ">"}
        self.quote_chars = {'"', "'", "`"}
        self.secondary_pattern = re.compile(r"[，,、；;]+")

        self.tmp_dir = "/tmp/astrbot_t2i_splitter"
        os.makedirs(self.tmp_dir, exist_ok=True)
        self._font_cache: dict = {}
        self._quote_cache = {"text": None, "ts": 0.0}
        self._quote_lock = threading.Lock()
        self._bg_cache = {"bytes": None, "ts": 0.0}
        self.bg_index = 0
        self.quote_index = 0

        self._status_cache = {"lines": None, "ts": 0.0}
        self._status_lock = threading.Lock()

        threading.Thread(target=self._quote_refresh_loop, daemon=True).start()

    def _cfg(self, key, default=None):
        try:
            return self.config.get(key, default) if isinstance(self.config, dict) else default
        except Exception:
            return default

    def _cfg_bool(self, key, default):
        v = self._cfg(key, default)
        if isinstance(v, bool): return v
        if isinstance(v, str): return v.lower() in ("true", "1", "yes", "on", "是", "开")
        return bool(v)

    def _cfg_int(self, key, default):
        try: return int(self._cfg(key, default))
        except Exception: return default

    def _cfg_str(self, key, default):
        v = self._cfg(key, default)
        return str(v) if v is not None else default

    def _get_now(self) -> datetime:
        return datetime.now(self.tz) if self.tz else datetime.now()

    def _load_font(self, size: int):
        if size in self._font_cache: return self._font_cache[size]
        for name in ["font.ttf", "font.ttc", "font.otf", "main.ttf", "custom.ttf"]:
            path = os.path.join(self.plugin_dir, name)
            if os.path.exists(path):
                try:
                    font = ImageFont.truetype(path, size)
                    self._font_cache[size] = font
                    return font
                except Exception: continue
        candidates = [
            "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
            "/usr/share/fonts/truetype/wqy/wqy-microhei.ttc",
            "C:/Windows/Fonts/msyh.ttc", "C:/Windows/Fonts/simhei.ttf",
            "/System/Library/Fonts/PingFang.ttc",
        ]
        for path in candidates:
            if os.path.exists(path):
                try:
                    font = ImageFont.truetype(path, size)
                    self._font_cache[size] = font
                    return font
                except Exception: continue
        font = ImageFont.load_default()
        self._font_cache[size] = font
        return font

    def _text_width(self, text: str, font) -> int:
        if not text: return 0
        try:
            bbox = font.getbbox(text)
            return bbox[2] - bbox[0]
        except AttributeError: return font.getsize(text)[0]

    def _text_height(self, text: str, font) -> int:
        if not text: return 0
        try:
            bbox = font.getbbox(text)
            return bbox[3] - bbox[1]
        except AttributeError: return font.getsize(text)[1]

    def _wrap_text(self, text: str, font, max_width: int):
        lines = []
        for raw_line in text.split("\n"):
            if not raw_line:
                lines.append("")
                continue
            cur = ""
            for ch in raw_line:
                test = cur + ch
                if self._text_width(test, font) <= max_width:
                    cur = test
                else:
                    if cur: lines.append(cur)
                    cur = ch
            if cur: lines.append(cur)
        return lines or [""]

    def _resolve_theme(self) -> str:
        if self.theme_mode == "浅色": return "light"
        if self.theme_mode == "深色": return "dark"
        h = self._get_now().hour
        return "dark" if (h >= self.dark_from or h < self.dark_to) else "light"

    def _get_system_status(self) -> List[str]:
        with self._status_lock:
            if self._status_cache["lines"] and (time.time() - self._status_cache["ts"]) < 30:
                return self._status_cache["lines"]

        lines = []
        if not HAS_PSUTIL:
            lines.append("⚠️ 未安装 psutil，无法获取详细状态")
        else:
            try:
                cpu_percent = psutil.cpu_percent(interval=None)
                mem = psutil.virtual_memory()
                disk = psutil.disk_usage('/')
                
                if self.status_detail == "简洁":
                    lines.append(f"💻 系统: {platform.system()} {platform.release()}")
                    lines.append(f"⚙️ CPU: {cpu_percent}%  |  🧠 内存: {mem.percent}%  |  💾 磁盘: {disk.percent}%")
                else:
                    lines.append(f"💻 系统: {platform.system()} {platform.release()} ({platform.machine()})")
                    lines.append(f"⚙️ CPU: {cpu_percent}%")
                    lines.append(f"🧠 内存: {mem.used // (1024**2)} MB / {mem.total // (1024**2)} MB ({mem.percent}%)")
                    lines.append(f"💾 磁盘: {disk.used // (1024**3)} GB / {disk.total // (1024**3)} GB ({disk.percent}%)")
                    uptime_seconds = time.time() - psutil.boot_time()
                    days, rem = divmod(uptime_seconds, 86400)
                    hours, rem = divmod(rem, 3600)
                    minutes, _ = divmod(rem, 60)
                    uptime_str = f"{int(days)}天 {int(hours)}小时 {int(minutes)}分" if days > 0 else f"{int(hours)}小时 {int(minutes)}分"
                    lines.append(f"⏱️ 运行时长: {uptime_str}")
            except Exception as e:
                logger.error(f"[T2I-Splitter] 获取系统状态失败: {e}")
                lines.append("⚠️ 获取系统状态时发生错误")

        with self._status_lock:
            self._status_cache["lines"] = lines
            self._status_cache["ts"] = time.time()
        return lines

    def _quote_refresh_loop(self):
        while True:
            try: self._fetch_quote_once()
            except Exception: pass
            time.sleep(1800)

    def _fetch_quote_once(self):
        if not HAS_REQUESTS or not self.quote_apis: return
        urls = self.quote_apis[self.quote_index:] + self.quote_apis[:self.quote_index]
        for url in urls:
            try:
                r = requests.get(url, timeout=4, headers={"User-Agent": "AstrBot-T2I/1.0"})
                if r.status_code != 200: continue
                data = r.json()
                text = ""
                if isinstance(data, dict):
                    text = (data.get("hitokoto") or (data.get("data") or {}).get("content") or data.get("content") or "")
                elif isinstance(data, str): text = data
                text = str(text).strip().strip('"').strip("'")
                if text:
                    with self._quote_lock:
                        self._quote_cache["text"] = text
                        self._quote_cache["ts"] = time.time()
                    self.quote_index = (self.quote_index + 1) % len(self.quote_apis)
                    return
            except Exception: continue

    def _get_quote(self) -> str:
        with self._quote_lock:
            text = self._quote_cache.get("text")
            ts = self._quote_cache.get("ts", 0)
        if text and (time.time() - ts) < 1800: return text
        try:
            if HAS_REQUESTS and self.quote_apis:
                self._fetch_quote_once()
                with self._quote_lock: text = self._quote_cache.get("text")
                if text: return text
        except Exception: pass
        return FALLBACK_QUOTES[self._get_now().timetuple().tm_yday % len(FALLBACK_QUOTES)]

    def _fetch_bg_image(self):
        if not self.bg_urls or not HAS_REQUESTS: return None
        if self._bg_cache["bytes"] and (time.time() - self._bg_cache["ts"]) < 300: return self._bg_cache["bytes"]
        urls = self.bg_urls[self.bg_index:] + self.bg_urls[:self.bg_index]
        for url in urls:
            try:
                r = requests.get(url, timeout=5, headers={"User-Agent": "Mozilla/5.0"})
                if r.status_code == 200:
                    try:
                        img = Image.open(io.BytesIO(r.content)); img.verify()
                        self._bg_cache["bytes"] = r.content
                        self._bg_cache["ts"] = time.time()
                        self.bg_index = (self.bg_index + 1) % len(self.bg_urls)
                        return r.content
                    except Exception: continue
            except Exception: continue
        return self._bg_cache["bytes"]

    def _create_base(self, width: int, height: int, colors: dict) -> Image.Image:
        bg_bytes = self._fetch_bg_image()
        if bg_bytes:
            try:
                bg_img = Image.open(io.BytesIO(bg_bytes)).convert("RGBA")
                bg_img = ImageOps.fit(bg_img, (width, height), Image.Resampling.LANCZOS)
                overlay = Image.new("RGBA", (width, height), (255, 255, 255, 20) if colors is LIGHT_THEME else (0, 0, 0, 40))
                return Image.alpha_composite(bg_img, overlay)
            except Exception: pass
        base = Image.new("RGBA", (width, height), (255, 255, 255, 255))
        draw = ImageDraw.Draw(base)
        c1, c2 = colors["bg_start"], colors["bg_end"]
        for y in range(height):
            t = y / max(height - 1, 1)
            draw.line([(0, y), (width, y)], fill=(int(c1[0]*(1-t)+c2[0]*t), int(c1[1]*(1-t)+c2[1]*t), int(c1[2]*(1-t)+c2[2]*t), 255))
        deco = Image.new("RGBA", (width, height), (0, 0, 0, 0))
        dd = ImageDraw.Draw(deco)
        primary, accent = colors["primary"], colors["accent"]
        dd.ellipse([(width - 380, -260), (width + 120, 240)], fill=(primary[0], primary[1], primary[2], 70))
        dd.ellipse([(-160, height - 260), (300, height + 160)], fill=(accent[0], accent[1], accent[2], 60))
        dd.ellipse([(width // 2 - 120, height // 3), (width // 2 + 320, height // 3 + 380)], fill=(primary[0], primary[1], primary[2], 30))
        deco = deco.filter(ImageFilter.GaussianBlur(70))
        return Image.alpha_composite(base, deco)

    def _draw_glass(self, base: Image.Image, box, radius: int, colors: dict):
        x1, y1, x2, y2 = box
        w, h = x2 - x1, y2 - y1
        if w <= 2 or h <= 2: return base
        shadow = Image.new("RGBA", (w + 20, h + 20), (0, 0, 0, 0))
        ImageDraw.Draw(shadow).rounded_rectangle([(10, 10), (w + 10, h + 10)], radius=radius, fill=(0, 0, 0, 35))
        shadow = shadow.filter(ImageFilter.GaussianBlur(12))
        base.alpha_composite(shadow, dest=(x1 - 10, y1 - 10))
        region = base.crop(box).filter(ImageFilter.GaussianBlur(45))
        mask = Image.new("L", (w, h), 0)
        ImageDraw.Draw(mask).rounded_rectangle([(0, 0), (w - 1, h - 1)], radius=radius, fill=255)
        base.paste(region, (x1, y1), mask)
        overlay = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        draw_overlay = ImageDraw.Draw(overlay)
        draw_overlay.rounded_rectangle([(0, 0), (w - 1, h - 1)], radius=radius, fill=colors["card_bg"])
        draw_overlay.rounded_rectangle([(1, 1), (w - 2, h - 2)], radius=radius - 1, outline=colors["card_border"], width=2)
        masked = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        masked.paste(overlay, (0, 0), mask)
        base.alpha_composite(masked, dest=(x1, y1))
        return base

    def _draw_local_glass(self, base: Image.Image, box, radius: int, colors: dict, bg_key="quote_bg", border_key="quote_border"):
        x1, y1, x2, y2 = box
        w, h = x2 - x1, y2 - y1
        if w <= 2 or h <= 2: return
        region = base.crop(box).filter(ImageFilter.GaussianBlur(20))
        mask = Image.new("L", (w, h), 0)
        ImageDraw.Draw(mask).rounded_rectangle([(0, 0), (w - 1, h - 1)], radius=radius, fill=255)
        base.paste(region, (x1, y1), mask)
        overlay = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        draw_overlay = ImageDraw.Draw(overlay)
        draw_overlay.rounded_rectangle([(0, 0), (w - 1, h - 1)], radius=radius, fill=colors[bg_key])
        draw_overlay.rounded_rectangle([(1, 1), (w - 2, h - 2)], radius=radius - 1, outline=colors[border_key], width=1)
        masked = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        masked.paste(overlay, (0, 0), mask)
        base.alpha_composite(masked, dest=(x1, y1))

    def _draw_header(self, draw, box, colors, font_brand, font_time, font_small):
        x1, y1, x2, y2 = box
        pad = 26
        now = self._get_now()
        h = now.hour
        greeting = "夜深了，早点休息" if h < 6 else "早上好" if h < 9 else "上午好" if h < 12 else "中午好" if h < 14 else "下午好" if h < 18 else "晚上好" if h < 22 else "夜深了，注意休息"
        brand_y = y1 + pad + 6
        draw.text((x1 + pad, brand_y), self.brand_name, font=font_brand, fill=colors["text"])
        draw.text((x1 + pad, brand_y + self._text_height(self.brand_name, font_brand) + 8), greeting, font=font_small, fill=colors["primary"])
        time_str = now.strftime("%H:%M:%S")
        date_full = f"{now.strftime('%Y-%m-%d')} · {['一', '二', '三', '四', '五', '六', '日'][now.weekday()]}"
        draw.text((x2 - pad - self._text_width(time_str, font_time), y1 + pad), time_str, font=font_time, fill=colors["primary"])
        draw.text((x2 - pad - self._text_width(date_full, font_small), y1 + pad + self._text_height(time_str, font_time) + 6), date_full, font=font_small, fill=colors["text_soft"])

    def _draw_content(self, draw, box, lines, colors, font, line_h, pad):
        cy = box[1] + pad
        for line in lines:
            if line: draw.text((box[0] + pad, cy), line, font=font, fill=colors["text"])
            cy += line_h

    def _render_text_to_png(self, text: str) -> bytes:
        theme = self._resolve_theme()
        colors = DARK_THEME if theme == "dark" else LIGHT_THEME
        font_brand, font_time = self._load_font(30), self._load_font(34)
        font_body, font_small, font_label = self._load_font(self.font_size), self._load_font(20), self._load_font(18)

        W, PAD, GAP, CPAD, RAD = max(600, self.card_width), 22, 16, 26, 28
        inner_w = W - PAD * 2 - CPAD * 2
        line_h_body = self.font_size + 12
        
        # 1. 预计算正文高度
        wrapped_body = self._wrap_text(text, font_body, inner_w)
        content_h = max(len(wrapped_body) * line_h_body + CPAD * 2, 70)
        
        # 2. 预计算一言高度 (动态计算实际行数)
        quote_h = 0
        wrapped_quote = []
        if self.show_quote:
            quote = self._get_quote()
            q_disp = f"「 {quote} 」"
            wrapped_quote = self._wrap_text(q_disp, font_small, inner_w - 32)
            label_h = self._text_height("每日一言", font_label)
            line_h_quote = self._text_height("测", font_small) + 8
            quote_h = label_h + 8 + len(wrapped_quote) * line_h_quote + 20 + CPAD * 2

        # 3. 预计算状态高度
        status_h = 0
        status_lines = self._get_system_status() if self.show_status else []
        if status_lines:
            label_h = self._text_height("服务器状态", font_label)
            line_h_status = self._text_height("测", font_small) + 8
            status_h = label_h + 8 + len(status_lines) * line_h_status + 20 + CPAD * 2

        # 4. 汇总卡片
        header_h = 118 if self.show_header else 0
        cards = []
        if header_h: cards.append(header_h)
        cards.append(content_h)
        if quote_h: cards.append(quote_h)
        if status_h: cards.append(status_h)

        total_h = PAD * 2 + sum(cards) + GAP * (len(cards) - 1)

        # 5. 绘制底图与卡片背景
        base = self._create_base(W, total_h, colors)
        boxes, y = [], PAD
        for h in cards:
            box = (PAD, y, W - PAD, y + h)
            base = self._draw_glass(base, box, RAD, colors)
            boxes.append(box)
            y += h + GAP

        # 6. 绘制文字
        draw = ImageDraw.Draw(base)
        idx = 0
        if self.show_header:
            self._draw_header(draw, boxes[idx], colors, font_brand, font_time, font_small)
            idx += 1
        
        self._draw_content(draw, boxes[idx], wrapped_body, colors, font_body, line_h_body, CPAD)
        idx += 1

        if self.show_quote:
            box = boxes[idx]
            y_quote = box[1] + CPAD
            draw.text((box[0] + CPAD, y_quote), "❝ 每日一言", font=font_label, fill=colors["primary"])
            qy = y_quote + self._text_height("每日一言", font_label) + 8
            q_box = (box[0] + CPAD, qy, box[2] - CPAD, qy + len(wrapped_quote) * (self._text_height("测", font_small) + 8) + 20)
            self._draw_local_glass(base, q_box, radius=18, colors=colors)
            text_cy = qy + 10
            for line in wrapped_quote:
                draw.text((box[0] + CPAD + 16, text_cy), line, font=font_small, fill=colors["text_soft"])
                text_cy += self._text_height("测", font_small) + 8
            idx += 1

        if self.show_status and status_lines:
            box = boxes[idx]
            y_status = box[1] + CPAD
            draw.text((box[0] + CPAD, y_status), "📊 服务器状态", font=font_label, fill=colors["primary"])
            sy = y_status + self._text_height("服务器状态", font_label) + 8
            s_box = (box[0] + CPAD, sy, box[2] - CPAD, sy + len(status_lines) * (self._text_height("测", font_small) + 8) + 20)
            self._draw_local_glass(base, s_box, radius=18, colors=colors, bg_key="status_bg", border_key="status_border")
            text_cy = sy + 10
            for line in status_lines:
                draw.text((box[0] + CPAD + 16, text_cy), line, font=font_small, fill=colors["text_soft"])
                text_cy += self._text_height("测", font_small) + 8

        buf = io.BytesIO()
        base.convert("RGB").save(buf, format="PNG", optimize=True)
        return buf.getvalue()

    def _cleanup_tmp(self):
        try:
            now = time.time()
            for f in os.listdir(self.tmp_dir):
                p = os.path.join(self.tmp_dir, f)
                if os.path.isfile(p) and now - os.path.getmtime(p) > 3600: os.remove(p)
        except Exception: pass

    def _save_png(self, img_bytes: bytes) -> str:
        self._cleanup_tmp()
        path = os.path.join(self.tmp_dir, f"{uuid.uuid4().hex}.png")
        with open(path, "wb") as f: f.write(img_bytes)
        return path

    def _get_conversation_key(self, event: AstrMessageEvent) -> str:
        return str(getattr(event, "unified_msg_origin", "") or "")

    def _get_processing_lock(self, conv_key: str) -> asyncio.Lock:
        if conv_key not in self._processing_locks:
            self._processing_locks[conv_key] = asyncio.Lock()
        return self._processing_locks[conv_key]

    def _build_split_pattern(self) -> str:
        processed = [re.escape(str(c).replace("\\n", "\n").replace("\\t", "\t")) for c in self.split_chars if c]
        processed.sort(key=len, reverse=True)
        return "(?:{})+".format("|".join(processed)) if processed else r"[\n]+"

    def _split_text(self, text: str, pattern: str, ideal: int, no_split_around: list) -> List[str]:
        compiled = re.compile(pattern)
        stack, i, n, chunk, weight, segments = [], 0, len(text), "", 0, []
        ratio_min, ratio_max = 0.4, 0.9
        while i < n:
            if text.startswith("```", i) and (i == 0 or text[i-1] == '\n'):
                idx = text.find("```", i + 3)
                if idx != -1: chunk += text[i:idx+3]; weight += idx + 3 - i; i = idx + 3; continue
                else: chunk += text[i:]; weight += n - i; break
            if text.startswith("<think>", i) and (i == 0 or text[i-1] == '\n'):
                idx = text.find("</think>", i + 7)
                if idx != -1: chunk += text[i:idx+8]; weight += idx + 8 - i; i = idx + 8; continue
                else: chunk += text[i:]; weight += n - i; break
            if (i == 0 or text[i-1] == '\n') and i < n and text[i] == '|':
                table_end, pos = i, i
                while pos < n:
                    line_end = text.find('\n', pos)
                    if line_end == -1: line_end = n
                    line = text[pos:line_end].strip()
                    if line.startswith('|') or (line and all(c in '-| :' for c in line)): table_end = line_end + 1 if line_end < n else n; pos = table_end
                    else: break
                if table_end > i + 1:
                    table_text = text[i:table_end]; chunk += table_text; weight += sum(1 for c in table_text if not c.isspace()); i = table_end; continue
            match = compiled.match(text, pos=i)
            if match:
                delim = match.group()
                should = False
                if not stack or "\n" in delim:
                    should = True
                    if ideal > 0 and weight < ideal * ratio_min: should = False
                    if should and "\n" not in delim and re.match(r"^[ \t.?!,;:\-']+$", delim):
                        p_c, n_c = text[i-1] if i > 0 else "", text[i+len(delim)] if i + len(delim) < n else ""
                        if re.match(r"^[a-zA-Z0-9 \t.?!,;:\-']$", p_c) and re.match(r"^[a-zA-Z0-9 \t.?!,;:\-']$", n_c): should = False
                    if should and no_split_around:
                        scan = i + len(delim)
                        while scan < n and text[scan] in ' \t': scan += 1
                        for word in no_split_around:
                            if word and scan + len(word) <= n and text[scan:scan+len(word)] == word: should = False; break
                if should: chunk += delim; segments.append(chunk); chunk = ""; weight = 0; i += len(delim)
                else: chunk += delim; weight += len(delim); i += len(delim)
                continue
            if ideal > 0 and weight >= ideal * ratio_max and not stack:
                sec = self.secondary_pattern.match(text, pos=i)
                if sec:
                    delim = sec.group(); chunk += delim; segments.append(chunk); chunk = ""; weight = 0; i += len(delim); continue
            char = text[i]
            if char in self.quote_chars:
                if stack and stack[-1] == char: stack.pop()
                else: stack.append(char)
            elif not stack and char in self.pair_map: stack.append(char)
            elif stack and char == self.pair_map.get(stack[-1]): stack.pop()
            chunk += char; i += 1; weight += 1 if not char.isspace() else 0
        if chunk: segments.append(chunk)
        return [s for s in segments if s.strip()]

    def _calculate_delay(self, next_text: str) -> float:
        return 0.5 + len(next_text) * 0.1

    @filter.on_llm_response()
    async def on_llm_response(self, event: AstrMessageEvent, resp):
        setattr(event, "__t2i_is_llm_reply", True)

    def _is_llm_reply(self, event: AstrMessageEvent, result) -> bool:
        if getattr(event, "__t2i_is_llm_reply", False): return True
        if not result: return False
        try:
            is_model_result = getattr(result, "is_model_result", None)
            if callable(is_model_result) and is_model_result(): return True
        except Exception: pass
        ct = getattr(result, "result_content_type", None)
        if ct is not None and getattr(ct, "name", "") in {"LLM_RESULT", "AGENT_RUNNER_ERROR", "AGENT_RUNNER_RESULT", "TOOL_RESULT", "TOOL_CALL"}: return True
        return False

    @filter.on_decorating_result(priority=-999999999999999999)
    async def on_decorating_result(self, event: AstrMessageEvent):
        try:
            result = event.get_result()
            if not result or not result.chain: return
            for comp in result.chain:
                if type(comp).__name__ in ("Image", "ImageComponent"): return
            if getattr(result, "__t2i_splitter_processed", False): return
            if sum(len(c.text) for c in result.chain if isinstance(c, Plain) and c.text) == 0: return
            if not self.enable_split: return
            if self.split_scope == "llm_only" and not self._is_llm_reply(event, result): return
            async with self._get_processing_lock(self._get_conversation_key(event)):
                await self._do_process(event, result)
        except Exception as e:
            logger.error(f"[T2I-Splitter] on_decorating_result 异常: {e}", exc_info=True)

    async def _do_process(self, event: AstrMessageEvent, result):
        setattr(result, "__t2i_splitter_processed", True)
        full_text_parts = []
        for comp in result.chain:
            if isinstance(comp, Plain) and comp.text:
                txt = comp.text
                for item in self.clean_before_items:
                    if item: txt = txt.replace(item, "")
                full_text_parts.append(txt)
        full_text = "\n".join(full_text_parts).strip()
        if not full_text: return

        pattern = self._build_split_pattern()
        ideal = max(math.ceil(len(full_text.replace(" ", "")) / max(1, self.max_segments)), self.min_segment_length) if self.max_segments > 1 else 0
        segments = self._split_text(full_text, pattern, ideal, self.no_split_around)

        if len(segments) > self.max_segments:
            segments = segments[:self.max_segments - 1] + ["".join(segments[self.max_segments - 1:])]
        if len(segments) >= 2 and 0 < len(segments[-1].strip()) < self.min_segment_length:
            segments[-2] += segments[-1]; segments.pop()
        segments = [s.strip() for s in segments if s.strip()]
        if not segments: return

        # ============ 单图模式 ============
        if self.image_render_mode == "单图保留分句":
            merged_text = "\n\n".join(segments)
            try:
                img_bytes = await asyncio.to_thread(self._render_text_to_png, merged_text)
                tmp_path = self._save_png(img_bytes)
                new_result = event.image_result(tmp_path)
                for comp in result.chain:
                    if not isinstance(comp, (Plain, Reply)): new_result.chain.append(comp)
                event.set_result(new_result)
            except Exception as e:
                logger.error(f"[T2I-Splitter] 单图渲染失败: {e}")
            return

        # ============ 多图分段模式 ============
        if len(segments) == 1:
            try:
                img_bytes = await asyncio.to_thread(self._render_text_to_png, segments[0])
                tmp_path = self._save_png(img_bytes)
                new_result = event.image_result(tmp_path)
                for comp in result.chain:
                    if not isinstance(comp, (Plain, Reply)): new_result.chain.append(comp)
                event.set_result(new_result)
            except Exception as e:
                logger.error(f"[T2I-Splitter] 单段渲染失败: {e}")
            return

        source_id = str(getattr(event.message_obj, "message_id", "") or "")
        for i in range(len(segments) - 1):
            seg_text = segments[i]
            try:
                img_bytes = await asyncio.to_thread(self._render_text_to_png, seg_text)
                tmp_path = self._save_png(img_bytes)
                mc = MessageChain()
                if i == 0 and self.enable_reply and source_id: mc.chain.append(Reply(id=source_id))
                mc.chain.append(event.image_result(tmp_path).chain[0])
                await self.context.send_message(event.unified_msg_origin, mc)
                await asyncio.sleep(self._calculate_delay(segments[i + 1]))
            except Exception as e:
                logger.error(f"[T2I-Splitter] 第 {i+1} 段发送失败: {e}")

        try:
            img_bytes = await asyncio.to_thread(self._render_text_to_png, segments[-1])
            tmp_path = self._save_png(img_bytes)
            new_result = event.image_result(tmp_path)
            for comp in result.chain:
                if not isinstance(comp, (Plain, Reply)): new_result.chain.append(comp)
            event.set_result(new_result)
        except Exception as e:
            logger.error(f"[T2I-Splitter] 末段渲染失败: {e}")

    @filter.command("t2i")
    async def t2i_cmd(self, event: AstrMessageEvent, text: str = None):
        content = text or "这是一条测试文本。\n换行测试。\nHello, AstrBot!"
        try:
            img_bytes = await asyncio.to_thread(self._render_text_to_png, content)
            yield event.image_result(self._save_png(img_bytes))
        except Exception as e:
            yield event.plain_result(f"生成失败: {e}")

    async def terminate(self): pass