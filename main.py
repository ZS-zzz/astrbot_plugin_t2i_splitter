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

# ============ 主题色板 (更通透的毛玻璃 & 高可读性 & 颜色统一) ============
LIGHT_THEME = {
    "bg_start":       (245, 249, 255),
    "bg_end":         (227, 242, 253),
    "text":           (20, 30, 40, 255),
    "text_soft":      (60, 75, 90, 255),
    "primary":        (25, 118, 210, 255),
    "accent":         (66, 165, 245, 255),
    "card_bg":        (255, 255, 255, 18),
    "card_border":    (255, 255, 255, 80),
    "quote_bg":       (30, 136, 229, 16),
    "quote_border":   (30, 136, 229, 60),
    "status_bg":      (30, 136, 229, 16),
    "status_border":  (30, 136, 229, 60),
}

DARK_THEME = {
    "bg_start":       (18, 31, 42),
    "bg_end":         (26, 44, 54),
    "text":           (240, 245, 255, 255),
    "text_soft":      (195, 210, 225, 255),
    "primary":        (100, 181, 246, 255),
    "accent":         (144, 202, 249, 255),
    "card_bg":        (15, 25, 35, 28),
    "card_border":    (255, 255, 255, 30),
    "quote_bg":       (100, 181, 246, 18),
    "quote_border":   (100, 181, 246, 70),
    "status_bg":      (100, 181, 246, 18),
    "status_border":  (100, 181, 246, 70),
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
    "文本转图片 + 智能分段融合插件 (Markdown 支持 & 布局修复 & 通透毛玻璃 & 高可读性 & 颜色统一 & 优化渲染)",
    "v1.6.7",
)
class ForceT2ISplitterPlugin(Star):

    _COLOR = object()  # 彩色 emoji 段标记

    _FONT_POOL = {
        "regular": [
            "font.ttf", "font.ttc", "font.otf", "main.ttf", "custom.ttf",
            "/usr/share/fonts/opentype/noto/NotoSansCJK-Regular.ttc",
            "/usr/share/fonts/truetype/wqy/wqy-microhei.ttc",
            "/usr/share/fonts/truetype/wqy/wqy-zenhei.ttc",
            "C:/Windows/Fonts/msyh.ttc",
            "C:/Windows/Fonts/simhei.ttf",
            "/System/Library/Fonts/PingFang.ttc",
        ],
        "bold": [
            "font_bold.ttf", "font_bold.ttc", "bold.ttf",
            "/usr/share/fonts/opentype/noto/NotoSansCJK-Bold.ttc",
            "/usr/share/fonts/truetype/noto/NotoSansCJK-Bold.ttc",
            "C:/Windows/Fonts/msyhbd.ttc",
        ],
        "mono": [
            "font_mono.ttf",
            "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf",
            "/usr/share/fonts/truetype/liberation/LiberationMono-Regular.ttf",
            "C:/Windows/Fonts/consola.ttf",
            "/System/Library/Fonts/Menlo.ttc",
        ],
    }

    # ============ 渲染性能调优参数 ============
    _BLUR_CARD    = 40
    _BLUR_LOCAL   = 20
    _BLUR_SHADOW  = 8
    _BLUR_DECO    = 45
    _GRADIENT_STEP = 4

    def __init__(self, context: Context, config: dict = None):
        super().__init__(context)
        self.config = config or {}
        self.plugin_dir = os.path.dirname(os.path.abspath(__file__))

        self.card_width    = self._cfg_int("卡片宽度", 1000)
        self.font_size     = self._cfg_int("字体大小", 28)
        self.theme_mode    = self._cfg_str("主题模式", "自动")
        self.brand_name    = self._cfg_str("品牌名称", "无名小服")
        self.show_header   = self._cfg_bool("显示头部", True)
        self.show_quote    = self._cfg_bool("显示每日一言", True)
        self.show_status   = self._cfg_bool("显示服务器状态", True)
        self.status_detail = self._cfg_str("状态详细程度", "简洁")
        self.image_render_mode = "单图保留分句"
        self.max_segments  = self._cfg_int("最大分段数", 1)
        self.enable_non_llm = self._cfg_bool("非LLM文本转图", False)

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
        self.send_speed = "自然"
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
        self._font_cmap: dict = {}
        self._font_cmap_by_path: dict = {}
        self._fallback_cache: dict = {}
        self._fallback_cmap = None
        self._color_font = None
        self._color_cmap = None
        self._color_loaded = False
        self._emoji_img_cache: dict = {}
        self._font_metrics_cache: dict = {}
        self._text_width_cache: dict = {}
        self._quote_cache = {"text": None, "ts": 0.0}
        self._quote_lock = threading.Lock()
        self._bg_cache = {"bytes": None, "ts": 0.0}
        self.bg_index = 0
        self.quote_index = 0

        self._status_cache = {"lines": None, "ts": 0.0}
        self._status_lock = threading.Lock()

        threading.Thread(target=self._quote_refresh_loop, daemon=True).start()

    # =========================================================
    #  配置读取
    # =========================================================
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

    # =========================================================
    #  字体管理
    # =========================================================
    def _resolve_font_path(self, bold=False, italic=False, mono=False):
        pools = []
        if mono:
            pools.append("mono")
        if bold:
            pools.append("bold")
        pools.append("regular")

        for pool_name in pools:
            for cand in self._FONT_POOL.get(pool_name, []):
                p = cand if os.path.isabs(cand) else os.path.join(self.plugin_dir, cand)
                if os.path.exists(p):
                    if pool_name == "bold":
                        return p, True
                    base = os.path.basename(p).lower()
                    is_bold = any(s in base for s in ("bold", "bd.", "heavy", "black"))
                    return p, is_bold
        return None, False

    def _load_font(self, size: int, bold=False, italic=False, mono=False):
        key = (size, bold, italic, mono)
        if key in self._font_cache:
            return self._font_cache[key]

        path, _ = self._resolve_font_path(bold=bold, italic=italic, mono=mono)
        if path:
            try:
                font = ImageFont.truetype(path, size)
                self._font_cache[key] = font
                if path not in self._font_cmap_by_path:
                    self._font_cmap_by_path[path] = self._read_cmap(path)
                self._font_cmap[id(font)] = self._font_cmap_by_path.get(path)
                return font
            except Exception:
                pass

        font = ImageFont.load_default()
        self._font_cache[key] = font
        return font

    @staticmethod
    def _read_cmap(path):
        """读取字体的 cmap 码点集合；解析失败返回 None（表示未知，不触发回退）"""
        try:
            from fontTools.ttLib import TTFont
            try:
                f = TTFont(path, lazy=True)
            except Exception:
                # .ttc 字体集合必须指定 fontNumber，逐个尝试
                for idx in range(8):
                    try:
                        f = TTFont(path, fontNumber=idx, lazy=True)
                    except (ValueError, IndexError, Exception):
                        break
                    try:
                        cmap = f.getBestCmap()
                    except Exception:
                        cmap = None
                    if cmap:
                        return set(cmap.keys())
                return None
            cmap = f.getBestCmap()
            return set(cmap.keys()) if cmap else None
        except Exception:
            return None

    def _load_fallback_font(self, size: int):
        """加载 Symbola 字体（font_symbols.ttf），用于渲染主字体缺失的 emoji/符号字形"""
        if size in self._fallback_cache:
            return self._fallback_cache[size]
        path = os.path.join(self.plugin_dir, "font_symbols.ttf")
        font = None
        if os.path.exists(path):
            try:
                font = ImageFont.truetype(path, size)
            except Exception:
                font = None
        self._fallback_cache[size] = font
        if font is not None and self._fallback_cmap is None:
            self._fallback_cmap = self._read_cmap(path)
        return font

    def _load_color_font(self):
        """懒加载 NotoColorEmoji（font_emoji.ttf，CBDT 彩色位图，固定 109px）"""
        if self._color_loaded:
            return
        self._color_loaded = True
        path = os.path.join(self.plugin_dir, "font_emoji.ttf")
        if os.path.exists(path):
            try:
                self._color_font = ImageFont.truetype(path, 109)
                self._color_cmap = self._read_cmap(path)
            except Exception:
                self._color_font = None
                self._color_cmap = None
        else:
            self._color_font = None

    def _render_colored_emoji(self, ch: str, size: int):
        """用 NotoColorEmoji 渲染彩色 emoji，返回 (RGBA Image, 逻辑宽度)；失败返回 (None, 0)"""
        size = max(4, int(size))
        key = (ch, size)
        cached = self._emoji_img_cache.get(key)
        if cached is not None:
            return cached
        self._load_color_font()
        if self._color_font is None:
            return (None, 0)
        try:
            f109 = self._color_font
            w = int(f109.getlength(ch)) + 2
            tmp = Image.new("RGBA", (max(w, 8), 128), (0, 0, 0, 0))
            td = ImageDraw.Draw(tmp)
            td.text((0, 0), ch, font=f109, embedded_color=True)
            bbox = tmp.getbbox()
            if not bbox:
                self._emoji_img_cache[key] = (None, 0)
                return (None, 0)
            tmp = tmp.crop(bbox)
            scale = size / 109.0
            nw = max(1, int(round(tmp.width * scale)))
            nh = max(1, int(round(tmp.height * scale)))
            img = tmp.resize((nw, nh), Image.LANCZOS)
            width = int(round(w * scale))
            result = (img, width)
            if len(self._emoji_img_cache) > 400:
                self._emoji_img_cache.clear()
            self._emoji_img_cache[key] = result
            return result
        except Exception:
            return (None, 0)

    def _split_by_font(self, text: str, font):
        """按字形覆盖拆分文本为 [(子串, 字体)]：主字体 → 彩色 emoji → Symbola 回退。
        彩色段字体标记为 self._COLOR，ZWJ/VS16 字符跟随前一段。"""
        if not text:
            return []
        cmap = self._font_cmap.get(id(font))
        if not cmap:
            return [(text, font)]
        self._load_color_font()
        size = getattr(font, "size", self.font_size)

        out = []
        cur_chars = []
        cur_kind = font
        for ch in text:
            if ch in "\u200d\ufe0f":
                # ZWJ / 变体选择符：并入当前段；若在行首被拆出（当前段为空）则归入彩色段（零宽，防豆腐块）
                if not cur_chars and self._color_cmap:
                    cur_kind = self._COLOR
                cur_chars.append(ch)
                continue
            kind = font
            cp = ord(ch)
            if cp not in cmap:
                if self._color_cmap and cp in self._color_cmap:
                    kind = self._COLOR
                elif self._fallback_cmap and cp in self._fallback_cmap:
                    kind = self._load_fallback_font(size) or font
            if kind is not cur_kind:
                if cur_chars:
                    out.append(("".join(cur_chars), cur_kind))
                    cur_chars = []
                cur_kind = kind
            cur_chars.append(ch)
        if cur_chars:
            out.append(("".join(cur_chars), cur_kind))
        return out

    def _measure_atom(self, atom: str, font) -> int:
        """测量 atom 的宽度，彩色 emoji / 符号按对应字体分别测宽"""
        if not atom:
            return 0
        segs = self._split_by_font(atom, font)
        if len(segs) == 1 and segs[0][1] is font:
            return self._text_width(atom, font)
        total = 0
        for sub, sub_font in segs:
            if sub_font is self._COLOR:
                _, w = self._render_colored_emoji(sub, getattr(font, "size", self.font_size))
                total += w
            else:
                total += self._text_width(sub, sub_font)
        return int(total)

    def _font_metrics(self, font):
        fid = id(font)
        cached = self._font_metrics_cache.get(fid)
        if cached is not None:
            return cached
        try:
            asc, desc = font.getmetrics()
        except Exception:
            asc, desc = 0, 0
        self._font_metrics_cache[fid] = (asc, desc)
        return asc, desc

    def _text_width(self, text: str, font) -> int:
        if not text:
            return 0
        key = (id(font), text)
        cached = self._text_width_cache.get(key)
        if cached is not None:
            return cached
        try:
            w = int(font.getlength(text))
        except AttributeError:
            try:
                bbox = font.getbbox(text)
                w = bbox[2] - bbox[0]
            except AttributeError:
                w = font.getsize(text)[0]
        if len(self._text_width_cache) > 4000:
            self._text_width_cache.clear()
        self._text_width_cache[key] = w
        return w

    def _text_height(self, text: str, font) -> int:
        if not text:
            return 0
        try:
            bbox = font.getbbox(text)
            return bbox[3] - bbox[1]
        except AttributeError:
            return font.getsize(text)[1]

    def _resolve_theme(self) -> str:
        if self.theme_mode == "浅色": return "light"
        if self.theme_mode == "深色": return "dark"
        h = self._get_now().hour
        return "dark" if (h >= self.dark_from or h < self.dark_to) else "light"

    # =========================================================
    #  Markdown 解析
    # =========================================================
    def _parse_inline(self, text: str) -> List[dict]:
        if not text:
            return []
        spans = []
        buf = []
        bold = italic = code = strike = False
        i, n = 0, len(text)

        def flush():
            if buf:
                spans.append({
                    "text": "".join(buf),
                    "bold": bold, "italic": italic,
                    "code": code, "strike": strike,
                })
                buf.clear()

        while i < n:
            ch = text[i]

            if code:
                if ch == "`":
                    flush(); code = False; i += 1; continue
                buf.append(ch); i += 1; continue

            if ch == "\\" and i + 1 < n and text[i + 1] in "\\`*_~[]()":
                buf.append(text[i + 1]); i += 2; continue

            if ch == "`":
                flush(); code = True; i += 1; continue

            if text.startswith("***", i):
                flush(); bold = not bold; italic = not italic; i += 3; continue
            if text.startswith("**", i):
                flush(); bold = not bold; i += 2; continue
            if ch == "*":
                flush(); italic = not italic; i += 1; continue
            if text.startswith("~~", i):
                flush(); strike = not strike; i += 2; continue

            if ch == "[":
                m = re.match(r'\[([^\]]*)\]\(([^)]*)\)', text[i:])
                if m:
                    flush()
                    spans.append({
                        "text": m.group(1), "link": True,
                        "bold": bold, "italic": italic,
                        "code": code, "strike": strike,
                    })
                    i += m.end(); continue

            buf.append(ch); i += 1

        flush()
        return spans

    def _split_table_row(self, line: str) -> List[str]:
        s = line.strip()
        if s.startswith("|"): s = s[1:]
        if s.endswith("|"): s = s[:-1]
        return [c.strip() for c in s.split("|")]

    def _is_block_start(self, line: str) -> bool:
        s = line.strip()
        if not s:
            return True
        if s.startswith("```"):
            return True
        if re.match(r'^#{1,6}\s', s):
            return True
        if s.startswith(">"):
            return True
        if re.match(r'^([-*+]|\d+[.)])\s+', s):
            return True
        if re.fullmatch(r'([-*_])(\s*\1){2,}', s):
            return True
        return False

    def _parse_markdown(self, text: str) -> List[dict]:
        blocks = []
        lines = text.split("\n")
        i, n = 0, len(lines)

        while i < n:
            line = lines[i]
            stripped = line.strip()

            if not stripped:
                i += 1
                continue

            # ============ 代码块：转为普通文本段落 ============
            m = re.match(r'^\s*```(.*)$', line)
            if m:
                i += 1
                code_lines = []
                while i < n and not re.match(r'^\s*```\s*$', lines[i]):
                    code_lines.append(lines[i])
                    i += 1
                if i < n:
                    i += 1
                raw = "\n".join(code_lines).rstrip()
                if raw.strip():
                    blocks.append({
                        "type": "paragraph",
                        "spans": [{
                            "text": raw,
                            "bold": False,
                            "italic": False,
                            "code": False,
                            "strike": False,
                        }],
                    })
                continue

            if re.fullmatch(r'\s*([-*_])(\s*\1){2,}\s*', line):
                blocks.append({"type": "hr"})
                i += 1
                continue

            m = re.match(r'^(#{1,6})\s+(.*?)\s*#*\s*$', stripped)
            if m:
                blocks.append({
                    "type": "heading",
                    "level": len(m.group(1)),
                    "spans": self._parse_inline(m.group(2)),
                })
                i += 1
                continue

            if stripped.startswith(">"):
                q_lines = []
                while i < n and lines[i].strip().startswith(">"):
                    q_lines.append(re.sub(r'^\s*>\s?', '', lines[i]))
                    i += 1
                blocks.append({
                    "type": "quote",
                    "children": self._parse_markdown("\n".join(q_lines)),
                })
                continue

            if re.match(r'^\s*([-*+]|\d+[.)])\s+', line):
                items = []
                while i < n and re.match(r'^\s*([-*+]|\d+[.)])\s+', lines[i]):
                    mm = re.match(r'^(\s*)([-*+]|\d+[.)])\s+(.*)$', lines[i])
                    if not mm:
                        break
                    indent = len(mm.group(1)) // 2
                    marker = mm.group(2)
                    ordered = bool(re.match(r'\d+', marker))
                    content = mm.group(3)
                    items.append({
                        "indent": indent,
                        "ordered": ordered,
                        "marker": marker if ordered else None,
                        "spans": self._parse_inline(content),
                    })
                    i += 1
                blocks.append({"type": "list", "items": items})
                continue

            if ("|" in line and i + 1 < n
                    and re.match(r'^\s*\|?[\s:|-]+\|[\s:|-]*$', lines[i + 1])
                    and "-" in lines[i + 1]):
                header = self._split_table_row(line)
                i += 2
                rows = []
                while i < n and "|" in lines[i] and lines[i].strip():
                    rows.append(self._split_table_row(lines[i]))
                    i += 1
                blocks.append({"type": "table", "header": header, "rows": rows})
                continue

            para = []
            while i < n and lines[i].strip() and not self._is_block_start(lines[i]):
                para.append(lines[i].strip())
                i += 1
            if para:
                blocks.append({
                    "type": "paragraph",
                    "spans": self._parse_inline("\n".join(para)),
                })

        return blocks

    # =========================================================
    #  富文本布局
    # =========================================================
    def _iter_atoms(self, text: str):
        buf = []
        for ch in text:
            if ch == "\n":
                if buf:
                    yield "".join(buf); buf.clear()
                yield "\n"
            elif ch == " ":
                if buf:
                    yield "".join(buf); buf.clear()
                yield " "
            elif ord(ch) < 128:
                buf.append(ch)
            else:
                if buf:
                    yield "".join(buf); buf.clear()
                yield ch
        if buf:
            yield "".join(buf)

    def _span_style(self, span, base_size, force_bold=False, force_mono=False):
        bold = bool(span.get("bold")) or force_bold
        italic = bool(span.get("italic"))
        mono = bool(span.get("code")) or force_mono
        return self._load_font(base_size, bold=bold, italic=italic, mono=mono)

    def _wrap_spans(self, spans, base_size, max_width, force_bold=False, force_mono=False):
        lines = []
        cur_line = []
        cur_w = 0

        def newline():
            nonlocal cur_line, cur_w
            lines.append(cur_line)
            cur_line = []
            cur_w = 0

        for span in spans:
            font = self._span_style(span, base_size, force_bold, force_mono)
            buf = ""

            for atom in self._iter_atoms(span.get("text", "")):
                if atom == "\n":
                    if buf:
                        cur_line.append({"text": buf, "font": font, "span": span})
                        buf = ""
                    newline()
                    continue

                atom_w = self._measure_atom(atom, font)
                if cur_w + atom_w > max_width and (cur_line or buf):
                    if buf:
                        cur_line.append({"text": buf, "font": font, "span": span})
                        buf = ""
                    newline()
                    if atom == " ":
                        continue
                buf += atom
                cur_w += atom_w

            if buf:
                cur_line.append({"text": buf, "font": font, "span": span})

        if cur_line or not lines:
            lines.append(cur_line)
        return lines

    def _markdown_layout(self, blocks, inner_w) -> List[dict]:
        items = []
        base = self.font_size

        for blk in blocks:
            t = blk.get("type")

            if t == "heading":
                lvl = blk.get("level", 1)
                extra = {1: 14, 2: 10, 3: 6, 4: 3, 5: 1, 6: 0}.get(lvl, 0)
                size = base + extra
                line_h = size + 12
                lines = self._wrap_spans(blk["spans"], size, inner_w, force_bold=True)
                items.append({
                    "kind": "heading", "lines": lines, "line_h": line_h,
                    "height": len(lines) * line_h + (14 if lvl <= 2 else 8),
                    "level": lvl,
                })

            elif t == "paragraph":
                line_h = base + 12
                lines = self._wrap_spans(blk["spans"], base, inner_w)
                items.append({
                    "kind": "para", "lines": lines, "line_h": line_h,
                    "height": len(lines) * line_h + 4,
                })

            elif t == "quote":
                sub = self._markdown_layout(blk.get("children", []), inner_w - 20)
                items.append({
                    "kind": "quote", "items": sub,
                    "height": sum(s["height"] for s in sub) + 16,
                })

            elif t == "list":
                line_h = base + 12
                rows = []
                for it in blk["items"]:
                    indent = it.get("indent", 0)
                    bullet = it.get("marker") or "•"
                    sub = self._wrap_spans(it["spans"], base, inner_w - 30 - indent * 18)
                    rows.append({"bullet": bullet, "lines": sub, "indent": indent})
                items.append({
                    "kind": "list", "rows": rows, "line_h": line_h,
                    "height": sum(len(r["lines"]) * line_h + 6 for r in rows) + 4,
                })

            elif t == "hr":
                items.append({"kind": "hr", "height": 26})

            elif t == "table":
                items.append(self._layout_table(blk, base, inner_w))

        return items

    def _layout_table(self, blk, base, inner_w):
        cols = max(1, len(blk["header"]))
        rows_raw = [blk["header"]] + blk.get("rows", [])
        col_w = max(60, inner_w // cols)
        line_h = base + 12

        rows = []
        for r in rows_raw:
            r = list(r) + [""] * (cols - len(r))
            r = r[:cols]
            cell_lines = [
                self._wrap_spans(self._parse_inline(c), base, col_w - 16)
                for c in r
            ]
            max_lines = max(1, max(len(cl) for cl in cell_lines))
            rows.append({"cells": cell_lines, "n_lines": max_lines})

        total_h = sum(r["n_lines"] * line_h for r in rows) + 12
        return {
            "kind": "table", "rows": rows, "cols": cols,
            "col_w": col_w, "line_h": line_h, "height": total_h,
        }

    # =========================================================
    #  绘制
    # =========================================================
    def _span_color(self, span, colors, default_key="text"):
        # 行内代码不再使用特殊颜色，统一为正文色
        if span.get("strike"):
            return colors["text_soft"]
        return colors[default_key]

    def _draw_spans_line(self, draw, line, colors, x, y, line_h, default_key="text"):
        if not line:
            return

        base_ascent, _ = self._font_metrics(line[0]["font"])

        cx = x
        for seg in line:
            text = seg.get("text", "")
            if not text:
                continue
            font = seg["font"]
            span = seg["span"]
            color = self._span_color(span, colors, default_key)

            for sub, sub_font in self._split_by_font(text, font):
                if sub_font is self._COLOR:
                    img, w = self._render_colored_emoji(sub, getattr(font, "size", self.font_size))
                    if img is not None:
                        yy = int(y + max(0, (line_h - img.height) // 2))
                        draw._image.paste(img, (int(cx), yy), img)
                    cx += w
                else:
                    w = self._text_width(sub, sub_font)
                    ascent, _ = self._font_metrics(sub_font)
                    dy = base_ascent - ascent
                    if dy < 0:
                        dy = 0
                    draw.text((cx, y + dy), sub, font=sub_font, fill=color)
                    cx += w

    def _draw_markdown_items(self, draw, items, colors, x, y, width):
        for it in items:
            kind = it["kind"]

            if kind in ("para", "heading"):
                cy = y
                for ln in it["lines"]:
                    self._draw_spans_line(draw, ln, colors, x, cy, it["line_h"])
                    cy += it["line_h"]
                if kind == "heading" and it["level"] <= 2:
                    cy += 4
                    draw.line([x, cy, x + width, cy], fill=colors["quote_border"], width=1)
                y += it["height"]

            elif kind == "quote":
                draw.rounded_rectangle(
                    [x, y + 4, x + 4, y + it["height"] - 4],
                    radius=2, fill=colors["quote_border"],
                )
                self._draw_markdown_items(draw, it["items"], colors,
                                          x + 16, y + 8, width - 16)
                y += it["height"]

            elif kind == "list":
                cy = y + 2
                font_b = self._load_font(self.font_size)
                for row in it["rows"]:
                    rx = x + row["indent"] * 18
                    try:
                        bh = font_b.getbbox(row["bullet"])[3]
                    except Exception:
                        bh = self.font_size
                    draw.text(
                        (rx, cy + (it["line_h"] - bh) // 2),
                        row["bullet"], font=font_b, fill=colors["primary"],
                    )
                    for ln in row["lines"]:
                        self._draw_spans_line(draw, ln, colors,
                                              rx + 26, cy, it["line_h"])
                        cy += it["line_h"]
                    cy += 6
                y += it["height"]

            elif kind == "hr":
                draw.line(
                    [x, y + it["height"] // 2, x + width, y + it["height"] // 2],
                    fill=colors["card_border"], width=2,
                )
                y += it["height"]

            elif kind == "table":
                cy = y + 6
                cols = it["cols"]
                col_w = it["col_w"]
                line_h = it["line_h"]

                for ri, row in enumerate(it["rows"]):
                    row_h = row["n_lines"] * line_h
                    if ri == 0:
                        draw.rectangle(
                            [x, cy, x + cols * col_w, cy + row_h],
                            fill=colors["quote_bg"],
                        )
                    for ci, cell in enumerate(row["cells"]):
                        ccx = x + ci * col_w + 8
                        ccy = cy
                        for ln in cell:
                            self._draw_spans_line(draw, ln, colors, ccx, ccy, line_h)
                            ccy += line_h
                    cy += row_h
                    draw.line([x, cy, x + cols * col_w, cy],
                              fill=colors["card_border"], width=1)

                draw.rectangle([x, y + 6, x + cols * col_w, cy],
                               outline=colors["card_border"], width=1)
                y += it["height"]

    def _draw_header(self, draw, box, colors, font_brand, font_time, font_small):
        x1, y1, x2, y2 = box
        pad = 26
        now = self._get_now()
        h = now.hour
        greeting = ("夜深了，早点休息" if h < 6 else
                    "早上好" if h < 9 else
                    "上午好" if h < 12 else
                    "中午好" if h < 14 else
                    "下午好" if h < 18 else
                    "晚上好" if h < 22 else
                    "夜深了，注意休息")
        brand_y = y1 + pad + 6
        draw.text((x1 + pad, brand_y), self.brand_name, font=font_brand, fill=colors["text"])
        draw.text((x1 + pad, brand_y + self._text_height(self.brand_name, font_brand) + 8),
                  greeting, font=font_small, fill=colors["primary"])

        time_str = now.strftime("%H:%M:%S")
        date_full = f"{now.strftime('%Y-%m-%d')} · {['一', '二', '三', '四', '五', '六', '日'][now.weekday()]}"
        draw.text((x2 - pad - self._text_width(time_str, font_time), y1 + pad),
                  time_str, font=font_time, fill=colors["primary"])
        draw.text((x2 - pad - self._text_width(date_full, font_small),
                   y1 + pad + self._text_height(time_str, font_time) + 6),
                  date_full, font=font_small, fill=colors["text_soft"])

    # =========================================================
    #  系统状态 / 每日一言 / 背景图
    # =========================================================
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
                    uptime_str = (f"{int(days)}天 {int(hours)}小时 {int(minutes)}分"
                                  if days > 0 else f"{int(hours)}小时 {int(minutes)}分")
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
            try:
                self._fetch_quote_once()
            except Exception:
                pass
            time.sleep(1800)

    def _fetch_quote_once(self):
        if not HAS_REQUESTS or not self.quote_apis:
            return
        urls = self.quote_apis[self.quote_index:] + self.quote_apis[:self.quote_index]
        for url in urls:
            try:
                r = requests.get(url, timeout=4, headers={"User-Agent": "AstrBot-T2I/1.0"})
                if r.status_code != 200:
                    continue
                data = r.json()
                text = ""
                if isinstance(data, dict):
                    text = (data.get("hitokoto")
                            or (data.get("data") or {}).get("content")
                            or data.get("content") or "")
                elif isinstance(data, str):
                    text = data
                text = str(text).strip().strip('"').strip("'")
                if text:
                    with self._quote_lock:
                        self._quote_cache["text"] = text
                        self._quote_cache["ts"] = time.time()
                    self.quote_index = (self.quote_index + 1) % len(self.quote_apis)
                    return
            except Exception:
                continue

    def _get_quote(self) -> str:
        with self._quote_lock:
            text = self._quote_cache.get("text")
            ts = self._quote_cache.get("ts", 0)
        if text and (time.time() - ts) < 1800:
            return text
        try:
            if HAS_REQUESTS and self.quote_apis:
                self._fetch_quote_once()
                with self._quote_lock:
                    text = self._quote_cache.get("text")
                if text:
                    return text
        except Exception:
            pass
        return FALLBACK_QUOTES[self._get_now().timetuple().tm_yday % len(FALLBACK_QUOTES)]

    def _fetch_bg_image(self):
        # 已停用：不再通过 API 获取背景图片（背景改为纯色）
        return None

    # =========================================================
    #  画布 & 卡片
    # =========================================================
    def _create_base(self, width: int, height: int, colors: dict, theme: str) -> Image.Image:
        # 纯色背景：不再请求 API 背景图，只用主题纯色；深浅模式由传入的 colors 决定
        bg = colors["bg_start"]
        return Image.new("RGBA", (width, height), (bg[0], bg[1], bg[2], 255))

    def _draw_glass(self, base: Image.Image, box, radius: int, colors: dict):
        x1, y1, x2, y2 = box
        w, h = x2 - x1, y2 - y1
        if w <= 2 or h <= 2:
            return base

        shadow = Image.new("RGBA", (w + 20, h + 20), (0, 0, 0, 0))
        ImageDraw.Draw(shadow).rounded_rectangle(
            [(10, 10), (w + 10, h + 10)], radius=radius, fill=(0, 0, 0, 20))
        shadow = shadow.filter(ImageFilter.GaussianBlur(self._BLUR_SHADOW))
        base.alpha_composite(shadow, dest=(x1 - 10, y1 - 10))

        region = base.crop(box).filter(ImageFilter.GaussianBlur(self._BLUR_CARD))
        mask = Image.new("L", (w, h), 0)
        ImageDraw.Draw(mask).rounded_rectangle([(0, 0), (w - 1, h - 1)], radius=radius, fill=255)
        base.paste(region, (x1, y1), mask)

        overlay = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        draw_overlay = ImageDraw.Draw(overlay)
        draw_overlay.rounded_rectangle([(0, 0), (w - 1, h - 1)], radius=radius, fill=colors["card_bg"])
        draw_overlay.rounded_rectangle([(1, 1), (w - 2, h - 2)], radius=radius - 1,
                                       outline=colors["card_border"], width=1)
        masked = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        masked.paste(overlay, (0, 0), mask)
        base.alpha_composite(masked, dest=(x1, y1))
        return base

    def _draw_local_glass(self, base: Image.Image, box, radius: int, colors: dict,
                          bg_key="quote_bg", border_key="quote_border"):
        x1, y1, x2, y2 = box
        w, h = x2 - x1, y2 - y1
        if w <= 2 or h <= 2:
            return

        region = base.crop(box).filter(ImageFilter.GaussianBlur(self._BLUR_LOCAL))
        mask = Image.new("L", (w, h), 0)
        ImageDraw.Draw(mask).rounded_rectangle([(0, 0), (w - 1, h - 1)], radius=radius, fill=255)
        base.paste(region, (x1, y1), mask)

        overlay = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        draw_overlay = ImageDraw.Draw(overlay)
        draw_overlay.rounded_rectangle([(0, 0), (w - 1, h - 1)], radius=radius, fill=colors[bg_key])
        draw_overlay.rounded_rectangle([(1, 1), (w - 2, h - 2)], radius=radius - 1,
                                       outline=colors[border_key], width=1)
        masked = Image.new("RGBA", (w, h), (0, 0, 0, 0))
        masked.paste(overlay, (0, 0), mask)
        base.alpha_composite(masked, dest=(x1, y1))

    # =========================================================
    #  图片编码
    # =========================================================
    def _encode_image(self, base_img: Image.Image) -> bytes:
        buf = io.BytesIO()
        base_img.convert("RGB").save(buf, format="PNG")
        return buf.getvalue()

    # =========================================================
    #  主渲染
    # =========================================================
    def _render_text_to_png(self, text: str) -> bytes:
        theme = self._resolve_theme()
        colors = DARK_THEME if theme == "dark" else LIGHT_THEME

        font_brand = self._load_font(30)
        font_time = self._load_font(34)
        font_small = self._load_font(20)
        font_label = self._load_font(18)

        W, PAD, GAP, CPAD, RAD = max(600, self.card_width), 22, 16, 26, 28
        inner_w = W - PAD * 2 - CPAD * 2

        blocks = self._parse_markdown(text)
        items = self._markdown_layout(blocks, inner_w)
        content_h = max(sum(it["height"] for it in items) + CPAD * 2, 70)

        quote_h = 0
        wrapped_quote = []
        if self.show_quote:
            quote = self._get_quote()
            q_disp = f"「 {quote} 」"
            wrapped_quote = self._wrap_text(q_disp, font_small, inner_w - 32)
            label_h = self._text_height("每日一言", font_label)
            line_h_quote = self._text_height("测", font_small) + 8
            quote_h = label_h + 8 + len(wrapped_quote) * line_h_quote + 20 + CPAD * 2

        status_h = 0
        status_lines = self._get_system_status() if self.show_status else []
        if status_lines:
            label_h = self._text_height("服务器状态", font_label)
            line_h_status = self._text_height("测", font_small) + 8
            status_h = label_h + 8 + len(status_lines) * line_h_status + 20 + CPAD * 2

        header_h = 118 if self.show_header else 0
        cards = []
        if header_h: cards.append(header_h)
        cards.append(content_h)
        if quote_h: cards.append(quote_h)
        if status_h: cards.append(status_h)

        total_h = PAD * 2 + sum(cards) + GAP * (len(cards) - 1)

        base = self._create_base(W, total_h, colors, theme)
        boxes, y = [], PAD
        for h in cards:
            box = (PAD, y, W - PAD, y + h)
            base = self._draw_glass(base, box, RAD, colors)
            boxes.append(box)
            y += h + GAP

        draw = ImageDraw.Draw(base)
        idx = 0

        if self.show_header:
            self._draw_header(draw, boxes[idx], colors, font_brand, font_time, font_small)
            idx += 1

        content_box = boxes[idx]
        self._draw_markdown_items(
            draw, items, colors,
            content_box[0] + CPAD,
            content_box[1] + CPAD,
            inner_w,
        )
        idx += 1

        if self.show_quote:
            box = boxes[idx]
            y_quote = box[1] + CPAD
            draw.text((box[0] + CPAD, y_quote), "❝ 每日一言",
                      font=font_label, fill=colors["primary"])
            qy = y_quote + self._text_height("每日一言", font_label) + 8
            lh = self._text_height("测", font_small) + 8
            q_box = (box[0] + CPAD, qy, box[2] - CPAD, qy + len(wrapped_quote) * lh + 20)
            self._draw_local_glass(base, q_box, radius=18, colors=colors)
            text_cy = qy + 10
            for line in wrapped_quote:
                draw.text((box[0] + CPAD + 16, text_cy), line,
                          font=font_small, fill=colors["text"])
                text_cy += lh
            idx += 1

        if self.show_status and status_lines:
            box = boxes[idx]
            y_status = box[1] + CPAD
            draw.text((box[0] + CPAD, y_status), "📊 服务器状态",
                      font=font_label, fill=colors["primary"])
            sy = y_status + self._text_height("服务器状态", font_label) + 8
            lh = self._text_height("测", font_small) + 8
            s_box = (box[0] + CPAD, sy, box[2] - CPAD, sy + len(status_lines) * lh + 20)
            self._draw_local_glass(base, s_box, radius=18, colors=colors,
                                   bg_key="status_bg", border_key="status_border")
            text_cy = sy + 10
            for line in status_lines:
                draw.text((box[0] + CPAD + 16, text_cy), line,
                          font=font_small, fill=colors["text"])
                text_cy += lh

        return self._encode_image(base)

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
                    if cur:
                        lines.append(cur)
                    cur = ch
            if cur:
                lines.append(cur)
        return lines or [""]

    # =========================================================
    #  临时文件
    # =========================================================
    def _cleanup_tmp(self):
        try:
            now = time.time()
            for f in os.listdir(self.tmp_dir):
                p = os.path.join(self.tmp_dir, f)
                if os.path.isfile(p) and now - os.path.getmtime(p) > 3600:
                    os.remove(p)
        except Exception:
            pass

    def _save_png(self, img_bytes: bytes) -> str:
        self._cleanup_tmp()
        path = os.path.join(self.tmp_dir, f"{uuid.uuid4().hex}.png")
        with open(path, "wb") as f:
            f.write(img_bytes)
        return path

    # =========================================================
    #  文本分段
    # =========================================================
    def _build_split_pattern(self) -> str:
        processed = [re.escape(str(c).replace("\\n", "\n").replace("\\t", "\t"))
                     for c in self.split_chars if c]
        processed.sort(key=len, reverse=True)
        return "(?:{})+".format("|".join(processed)) if processed else r"[\n]+"

    def _split_text(self, text: str, pattern: str, ideal: int, no_split_around: list) -> List[str]:
        compiled = re.compile(pattern)
        stack, i, n, chunk, weight, segments = [], 0, len(text), "", 0, []
        ratio_min, ratio_max = 0.4, 0.9

        while i < n:
            if text.startswith("```", i) and (i == 0 or text[i - 1] == '\n'):
                idx = text.find("```", i + 3)
                if idx != -1:
                    chunk += text[i:idx + 3]; weight += idx + 3 - i; i = idx + 3; continue
                else:
                    chunk += text[i:]; weight += n - i; break

            if text.startswith("<think>", i) and (i == 0 or text[i - 1] == '\n'):
                idx = text.find("</think>", i + 7)
                if idx != -1:
                    chunk += text[i:idx + 8]; weight += idx + 8 - i; i = idx + 8; continue
                else:
                    chunk += text[i:]; weight += n - i; break

            if (i == 0 or text[i - 1] == '\n') and i < n and text[i] == '|':
                table_end, pos = i, i
                while pos < n:
                    line_end = text.find('\n', pos)
                    if line_end == -1:
                        line_end = n
                    line = text[pos:line_end].strip()
                    if line.startswith('|') or (line and all(c in '-| :' for c in line)):
                        table_end = line_end + 1 if line_end < n else n
                        pos = table_end
                    else:
                        break
                if table_end > i + 1:
                    table_text = text[i:table_end]
                    chunk += table_text
                    weight += sum(1 for c in table_text if not c.isspace())
                    i = table_end
                    continue

            match = compiled.match(text, pos=i)
            if match:
                delim = match.group()
                should = False
                if not stack or "\n" in delim:
                    should = True
                    if ideal > 0 and weight < ideal * ratio_min:
                        should = False
                    if should and "\n" not in delim and re.match(r"^[ \t.?!,;:\-']+$", delim):
                        p_c = text[i - 1] if i > 0 else ""
                        n_c = text[i + len(delim)] if i + len(delim) < n else ""
                        if (re.match(r"^[a-zA-Z0-9 \t.?!,;:\-']$", p_c)
                                and re.match(r"^[a-zA-Z0-9 \t.?!,;:\-']$", n_c)):
                            should = False
                    if should and no_split_around:
                        scan = i + len(delim)
                        while scan < n and text[scan] in ' \t':
                            scan += 1
                        for word in no_split_around:
                            if word and scan + len(word) <= n and text[scan:scan + len(word)] == word:
                                should = False
                                break
                if should:
                    chunk += delim; segments.append(chunk); chunk = ""; weight = 0; i += len(delim)
                else:
                    chunk += delim; weight += len(delim); i += len(delim)
                continue

            if ideal > 0 and weight >= ideal * ratio_max and not stack:
                sec = self.secondary_pattern.match(text, pos=i)
                if sec:
                    delim = sec.group()
                    chunk += delim; segments.append(chunk); chunk = ""; weight = 0
                    i += len(delim)
                    continue

            char = text[i]
            if char in self.quote_chars:
                if stack and stack[-1] == char: stack.pop()
                else: stack.append(char)
            elif not stack and char in self.pair_map:
                stack.append(char)
            elif stack and char == self.pair_map.get(stack[-1]):
                stack.pop()
            chunk += char
            i += 1
            weight += 1 if not char.isspace() else 0

        if chunk:
            segments.append(chunk)
        return [s for s in segments if s.strip()]

    # =========================================================
    #  事件处理
    # =========================================================
    def _get_conversation_key(self, event: AstrMessageEvent) -> str:
        return str(getattr(event, "unified_msg_origin", "") or "")

    def _get_processing_lock(self, conv_key: str) -> asyncio.Lock:
        if conv_key not in self._processing_locks:
            self._processing_locks[conv_key] = asyncio.Lock()
        return self._processing_locks[conv_key]

    @filter.on_llm_response()
    async def on_llm_response(self, event: AstrMessageEvent, resp):
        setattr(event, "__t2i_is_llm_reply", True)

    def _is_llm_reply(self, event: AstrMessageEvent, result) -> bool:
        if getattr(event, "__t2i_is_llm_reply", False):
            return True
        if not result:
            return False
        ct = getattr(result, "result_content_type", None)
        ct_name = getattr(ct, "name", "") if ct is not None else ""
        if ct_name in ("TOOL_RESULT", "TOOL_CALL", "AGENT_RUNNER_ERROR"):
            return False
        if ct_name in ("LLM_RESULT", "AGENT_RUNNER_RESULT"):
            return True
        if callable(getattr(result, "is_model_result", None)):
            try:
                if result.is_model_result():
                    return True
            except Exception:
                pass
        return False

    @filter.on_decorating_result(priority=-999999999999999999)
    async def on_decorating_result(self, event: AstrMessageEvent):
        try:
            result = event.get_result()
            if not result or not result.chain:
                return
            for comp in result.chain:
                if type(comp).__name__ in ("Image", "ImageComponent"):
                    return
            if getattr(result, "__t2i_splitter_processed", False):
                return
            if sum(len(c.text) for c in result.chain if isinstance(c, Plain) and c.text) == 0:
                return
            if not self.enable_split:
                return

            is_llm = self._is_llm_reply(event, result)
            if not is_llm and not self.enable_non_llm:
                return

            async with self._get_processing_lock(self._get_conversation_key(event)):
                await self._do_process(event, result)
        except Exception as e:
            logger.error(f"[T2I-Splitter] on_decorating_result 异常: {e}", exc_info=True)

    async def _do_process(self, event: AstrMessageEvent, result):
        setattr(result, "__t2i_splitter_processed", True)
        try:
            full_text_parts = []
            for comp in result.chain:
                text = getattr(comp, "text", None)
                if isinstance(text, str) and text:
                    full_text_parts.append(text)
            full_text = "\n".join(full_text_parts)
            if not full_text.strip():
                return

            if self.max_segments <= 1:
                merged_text = full_text
            else:
                pattern = self._build_split_pattern()
                ideal = max(
                    math.ceil(len(full_text.replace(" ", "")) / max(1, self.max_segments)),
                    self.min_segment_length,
                )
                segments = self._split_text(full_text, pattern, ideal, self.no_split_around)

                if len(segments) > self.max_segments:
                    head = segments[: self.max_segments - 1]
                    tail = "\n\n".join(segments[self.max_segments - 1:])
                    segments = head + [tail]

                if len(segments) >= 2 and 0 < len(segments[-1].strip()) < self.min_segment_length:
                    segments[-2] = segments[-2].rstrip() + "\n\n" + segments[-1].lstrip()
                    segments.pop()

                segments = [s for s in segments if s.strip()]
                if not segments:
                    return

                merged_text = "\n\n".join(s.strip() for s in segments)

            logger.info(
                f"[T2I-Splitter] 渲染文本 len={len(merged_text)}, "
                f"preview={merged_text[:160]!r}"
            )
            try:
                img_bytes = await asyncio.to_thread(self._render_text_to_png, merged_text)
                tmp_path = self._save_png(img_bytes)
                new_result = event.image_result(tmp_path)
                for comp in result.chain:
                    if not isinstance(comp, (Plain, Reply)):
                        new_result.chain.append(comp)
                event.set_result(new_result)
            except Exception as e:
                logger.error(f"[T2I-Splitter] 单图渲染失败: {e}", exc_info=True)
        except Exception as e:
            logger.error(f"[T2I-Splitter] _do_process 异常: {e}", exc_info=True)

    @filter.command("t2i")
    async def t2i_cmd(self, event: AstrMessageEvent, text: str = None):
        content = text or (
            "# 测试标题\n\n"
            "这是一条 **粗体**、*斜体*、`行内代码` 和 ~~删除线~~ 的测试文本。\n\n"
            "- 列表项一\n- 列表项二\n\n"
            "> 引用文字示例\n\n"
            "```python\nprint('hello')\n```\n"
        )
        try:
            img_bytes = await asyncio.to_thread(self._render_text_to_png, content)
            yield event.image_result(self._save_png(img_bytes))
        except Exception as e:
            yield event.plain_result(f"生成失败: {e}")

    async def terminate(self):
        pass
