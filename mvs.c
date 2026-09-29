/*
 * mvs - a text stripper
 *
 *   build:  cc mvs.c -o mvs
 *   use:    mvs [-c] [-d] [file]        (reads stdin if no file is given)
 *
 *   default  cleaned text -> stdout, findings -> stderr
 *   -c       check only: no text output, exit status 1 if anything found
 *   -d       also try to decode hidden payloads (tag text, bits, bytes)
 *
 * Pipeline (each stage consumes the previous one's output, no AST):
 *
 *   bytes --dec--> codepoints --homoglyphs--> --strip runs--> --trailing ws--> bytes
 *
 * Deliberate omissions (this is the "smallest" version):
 *   - no NFC/NFKC (needs big tables); fullwidth/math letters are folded by
 *     arithmetic and ~40 Cyrillic/Greek lookalikes by a tiny table
 *   - no directory recursion: use  find . -name '*.md' | xargs -n1 mvs -c
 *   - the range table is a strong start, not the full list of Cf characters
 *
 * Quiet normalizations (NOT counted as "found"): exotic spaces -> ' ',
 * CR / CRLF / U+0085 / U+2028 / U+2029 -> '\n'.
 */
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned U;                       /* a Unicode codepoint */

/* ---- 1. character classes ------------------------------------------- */

enum { OK, INVIS, JOIN, BIDI, TAG, VSEL, BOM, PUA, SPACE, NL, CTRL, BAD };

/* One row per range. Anything not listed is OK (kept as-is). */
static const struct { U lo, hi; int k; } R[] = {
    /* invisible / format characters: always stripped */
    {0x00AD, 0x00AD, INVIS},              /* soft hyphen                    */
    {0x034F, 0x034F, INVIS},              /* combining grapheme joiner      */
    {0x115F, 0x1160, INVIS},              /* hangul choseong/jungseong fill */
    {0x17B4, 0x17B5, INVIS},              /* khmer inherent vowels          */
    {0x180B, 0x180F, INVIS},              /* mongolian selectors + U+180E   */
    {0x200B, 0x200B, INVIS},              /* zero width space               */
    {0x2060, 0x2064, INVIS},              /* word joiner, invisible ops     */
    {0x206A, 0x206F, INVIS},              /* deprecated format chars        */
    {0x2800, 0x2800, INVIS},              /* braille blank                  */
    {0x3164, 0x3164, INVIS},              /* hangul filler                  */
    {0xFFA0, 0xFFA0, INVIS},              /* halfwidth hangul filler        */
    {0xFFF9, 0xFFFB, INVIS},              /* interlinear annotation         */
    {0x1D173, 0x1D17A, INVIS},            /* musical format controls        */
    /* ZWNJ / ZWJ: legit inside emoji and Arabic/Indic text -> see sus()   */
    {0x200C, 0x200D, JOIN},
    /* directional marks, embeddings, overrides, isolates ("Trojan Source") */
    {0x200E, 0x200F, BIDI},
    {0x202A, 0x202E, BIDI},
    {0x2066, 0x2069, BIDI},
    /* variation selectors: legit after one emoji/CJK base, else stego     */
    {0xFE00, 0xFE0F, VSEL},
    {0xE0100, 0xE01EF, VSEL},
    /* BOM: fine at offset 0, suspicious anywhere else                     */
    {0xFEFF, 0xFEFF, BOM},
    /* tag block U+E0000..E007F: invisible ASCII, used for LLM tracking    */
    {0xE0000, 0xE007F, TAG},
    /* private use areas                                                   */
    {0xE000, 0xF8FF, PUA},
    {0xF0000, 0xFFFFD, PUA},
    {0x100000, 0x10FFFD, PUA},
    /* spaces -> ' ' (quiet) */
    {0x00A0, 0x00A0, SPACE},
    {0x1680, 0x1680, SPACE},
    {0x2000, 0x200A, SPACE},              /* en/em/thin/hair... spaces      */
    {0x202F, 0x202F, SPACE},
    {0x205F, 0x205F, SPACE},
    {0x3000, 0x3000, SPACE},
    /* line breaks -> '\n' (quiet) */
    {0x000D, 0x000D, NL},
    {0x0085, 0x0085, NL},
    {0x2028, 0x2029, NL},
    /* control characters except \t \n \r (C1 minus U+0085) */
    {0x0000, 0x0008, CTRL},
    {0x000B, 0x000C, CTRL},
    {0x000E, 0x001F, CTRL},
    {0x007F, 0x0084, CTRL},
    {0x0086, 0x009F, CTRL},
};

static int cls(U c) {
    if (c >= 0x110000) return BAD;        /* sentinel for invalid UTF-8 byte */
    for (size_t i = 0; i < sizeof R / sizeof *R; i++)
        if (c >= R[i].lo && c <= R[i].hi) return R[i].k;
    return OK;
}

/* ---- 2. UTF-8 in and out -------------------------------------------- */

/* Decode one codepoint from s. Returns its byte length, or 0 if invalid
 * (bad lead byte, truncated, bad continuation, overlong, surrogate, >10FFFF). */
static int dec(const unsigned char *s, size_t len, U *c) {
    int l = s[0] < 0x80 ? 1
          : s[0] >= 0xC2 && s[0] <= 0xDF ? 2
          : (s[0] & 0xF0) == 0xE0 ? 3
          : s[0] >= 0xF0 && s[0] <= 0xF4 ? 4 : 0;
    if (!l || (size_t)l > len) return 0;
    U v = l == 1 ? s[0] : s[0] & (0xFF >> (l + 1));
    for (int i = 1; i < l; i++) {
        if ((s[i] & 0xC0) != 0x80) return 0;
        v = v << 6 | (s[i] & 0x3F);
    }
    if ((l == 3 && v < 0x800) || (l == 4 && v < 0x10000) ||
        v > 0x10FFFF || (v >= 0xD800 && v <= 0xDFFF)) return 0;
    *c = v;
    return l;
}

static void put(U c) {
    if (c < 0x80) putchar(c);
    else if (c < 0x800) { putchar(0xC0 | c >> 6); putchar(0x80 | (c & 0x3F)); }
    else if (c < 0x10000) {
        putchar(0xE0 | c >> 12);
        putchar(0x80 | (c >> 6 & 0x3F));
        putchar(0x80 | (c & 0x3F));
    } else {
        putchar(0xF0 | c >> 18);
        putchar(0x80 | (c >> 12 & 0x3F));
        putchar(0x80 | (c >> 6 & 0x3F));
        putchar(0x80 | (c & 0x3F));
    }
}

/* ---- 3. shared state ------------------------------------------------ */

static U *cp;                             /* decoded input                  */
static size_t n;                          /* number of codepoints in cp     */
static U *out;                            /* cleaned text (also codepoints) */
static size_t m;                          /* number of codepoints in out    */
static int found;                         /* # of suspicious findings       */
static int want_decode;                   /* -d                             */

/* ---- 4. context rules: is this hidden-class char actually suspicious? -- */

static int emo(U c) {                     /* rough "is emoji-ish" test      */
    return (c >= 0x1F000 && c <= 0x1FAFF) || (c >= 0x2190 && c <= 0x2BFF) ||
           c == 0xFE0F;
}
static int rtl_indic(U c) {               /* Arabic/Persian or Indic block  */
    return (c >= 0x600 && c <= 0x77F) || (c >= 0x900 && c <= 0xDFF);
}

/* Should cp[i] be stripped and reported? */
static int sus(size_t i) {
    U c = cp[i], p = i ? cp[i - 1] : 0, q = i + 1 < n ? cp[i + 1] : 0;
    switch (cls(c)) {
    case JOIN:   /* keep only between two emoji, or two Arabic/Indic letters */
        return !((emo(p) && emo(q)) || (rtl_indic(p) && rtl_indic(q)));
    case VSEL:   /* keep a lone selector after a real base char (or keycap) */
        return !((p >= 0x80 || (p && strchr("#*0123456789", p))) &&
                 cls(p) == OK && cls(q) != VSEL);
    case BOM:    return i != 0;
    case INVIS: case BIDI: case TAG: case PUA: case CTRL: case BAD: return 1;
    }
    return 0;
}

/* Runs are grouped by "family" so tags, selectors and the rest decode apart. */
static int fam(U c) {
    int k = cls(c);
    return k == TAG ? TAG : k == VSEL ? VSEL : INVIS;
}

/* ---- 5. payload decoding (-d) --------------------------------------- */

static void show(const char *what, const unsigned char *b, size_t nb) {
    fprintf(stderr, "  %s: \"", what);
    for (size_t i = 0; i < nb; i++)
        fputc(b[i] >= 32 && b[i] < 127 ? b[i] : '.', stderr);
    fputs("\"\n", stderr);
}

/* Try to read a hidden message out of the run cp[at .. at+len). */
static void payload(size_t at, size_t len) {
    const U *r = cp + at;
    unsigned char b[256] = {0};
    size_t nb = 0, i;
    int f = fam(r[0]);

    if (f == TAG) {                       /* U+E0020..E007E = ASCII + 0xE0000 */
        for (i = 0; i < len && nb < sizeof b; i++)
            if (r[i] >= 0xE0020 && r[i] <= 0xE007E) b[nb++] = r[i] - 0xE0000;
        if (nb) show("tag text", b, nb);
    } else if (f == VSEL) {               /* one selector per byte (emoji smuggling) */
        for (i = 0; i < len && nb < sizeof b; i++)
            b[nb++] = r[i] <= 0xFE0F ? r[i] - 0xFE00 : r[i] - 0xE0100 + 16;
        show("selector bytes", b, nb);
    } else if (len >= 8) {                /* binary stego: two symbols = 0 and 1 */
        U u[8];
        size_t fq[8] = {0}, d = 0, x, t1 = 0, t2 = 1, bits = 0;
        for (i = 0; i < len; i++) {       /* tally up to 8 distinct symbols  */
            for (x = 0; x < d && u[x] != r[i]; x++) ;
            if (x == d && d < 8) u[d++] = r[i];
            if (x < d) fq[x]++;
        }
        if (d < 2) return;
        if (fq[1] > fq[0]) { t1 = 1; t2 = 0; }
        for (x = 2; x < d; x++)           /* two most frequent = the bit symbols */
            if (fq[x] > fq[t1]) { t2 = t1; t1 = x; }
            else if (fq[x] > fq[t2]) t2 = x;
        U zero = u[t1] < u[t2] ? u[t1] : u[t2];   /* convention: lower cp = 0 */
        U one  = u[t1] < u[t2] ? u[t2] : u[t1];
        for (i = 0; i < len && bits / 8 < sizeof b; i++) {
            if (r[i] != zero && r[i] != one) continue;   /* separators */
            if (r[i] == one) b[bits / 8] |= 0x80 >> (bits % 8);
            bits++;
        }
        if (bits >= 8) show("bit payload", b, bits / 8);
    }
}

/* ---- 6. homoglyphs -------------------------------------------------- */

/* Cyrillic/Greek letters that look like Latin ones. Sentinel row at the end. */
static const struct { U u; char a; } L[] = {
    {0x0410,'A'},{0x0412,'B'},{0x0415,'E'},{0x041A,'K'},{0x041C,'M'},
    {0x041D,'H'},{0x041E,'O'},{0x0420,'P'},{0x0421,'C'},{0x0422,'T'},
    {0x0425,'X'},{0x0430,'a'},{0x0435,'e'},{0x043E,'o'},{0x0440,'p'},
    {0x0441,'c'},{0x0443,'y'},{0x0445,'x'},{0x0455,'s'},{0x0456,'i'},
    {0x0458,'j'},
    {0x0391,'A'},{0x0392,'B'},{0x0395,'E'},{0x0396,'Z'},{0x0397,'H'},
    {0x0399,'I'},{0x039A,'K'},{0x039C,'M'},{0x039D,'N'},{0x039F,'O'},
    {0x03A1,'P'},{0x03A4,'T'},{0x03A5,'Y'},{0x03A7,'X'},{0x03BF,'o'},
    {0x03BD,'v'},
    {0, 0}
};
static char look(U c) {
    for (const typeof(*L) *p = L; p->u; p++) if (p->u == c) return p->a;
    return 0;
}

/* Fullwidth letters/digits and math alphanumerics -> plain ASCII, or 0. */
static U arith(U c) {
    if (c >= 0xFF01 && c <= 0xFF5E && isalnum((int)(c - 0xFEE0)))
        return c - 0xFEE0;                            /* Ａ -> A, ０ -> 0 */
    if (c >= 0x1D400 && c <= 0x1D6A3) {               /* 13 styles x (A-Z a-z) */
        c = (c - 0x1D400) % 52;
        return c < 26 ? 'A' + c : 'a' + c - 26;       /* 𝔉𝔯𝔞𝔨𝔱𝔲𝔯, 𝐛𝐨𝐥𝐝, 𝚖𝚘𝚗𝚘 ... */
    }
    if (c >= 0x1D7CE && c <= 0x1D7FF) return '0' + (c - 0x1D7CE) % 10;
    return 0;
}

/* A "word" char is ASCII alnum, or any non-space non-ASCII char. */
static int wordc(U c) {
    return c < 0x80 ? isalnum((int)c) != 0 : cls(c) != SPACE && cls(c) != NL;
}

static void homoglyphs(void) {
    size_t i, j, k, folded = 0;

    for (i = 0; i < n; i++) {             /* pass 1: unconditional folds     */
        U a = arith(cp[i]);
        if (a) { cp[i] = a; folded++; }
    }
    if (folded) {
        found++;
        fprintf(stderr, "%zu fullwidth/math letters folded to ASCII\n", folded);
    }

    /* pass 2: lookalikes, but ONLY inside words that also contain Latin
     * letters. A purely Russian word full of Cyrillic "а" and "о" is real
     * text and must be left alone. */
    for (i = 0; i < n; i = j) {
        size_t na = 0, nl = 0, no = 0;    /* ascii letters, lookalikes, others */
        for (j = i; j < n && wordc(cp[j]); j++) {
            if (cp[j] < 0x80) na += isalpha((int)cp[j]) != 0;
            else if (look(cp[j])) nl++;
            else if (cls(cp[j]) == OK) no++;
        }
        if (j == i) { j++; continue; }    /* not a word char: step over it   */
        if (na && nl) {
            found++;
            fprintf(stderr, "char %zu: %zu lookalike letter(s) inside a Latin word%s\n",
                    i, nl, no ? " (kept: word has other non-Latin letters)" : "");
            if (!no)                       /* safe to fold: result is pure ASCII */
                for (k = i; k < j; k++) if (look(cp[k])) cp[k] = look(cp[k]);
        }
    }
}

/* ---- 7. strip hidden runs, normalize spaces/newlines ---------------- */

static void strip(void) {
    for (size_t i = 0; i < n; ) {
        if (sus(i)) {                     /* collect the whole run, report once */
            size_t j = i;
            while (j < n && sus(j) && fam(cp[j]) == fam(cp[i])) j++;
            found++;
            if (cp[i] >= 0x110000)
                fprintf(stderr, "char %zu: invalid UTF-8 byte 0x%02X\n", i, cp[i] - 0x110000);
            else
                fprintf(stderr, "char %zu: %zu hidden char(s), first U+%04X\n", i, j - i, cp[i]);
            if (want_decode) payload(i, j - i);
            i = j;
            continue;
        }
        switch (cls(cp[i])) {
        case SPACE: out[m++] = ' '; break;
        case NL:                          /* CRLF counts as one newline      */
            if (cp[i] == '\r' && i + 1 < n && cp[i + 1] == '\n') i++;
            out[m++] = '\n';
            break;
        default: out[m++] = cp[i];
        }
        i++;
    }
}

/* ---- 8. trailing-whitespace stego ----------------------------------- */

/* Markdown uses exactly two trailing spaces as a hard break, so those and
 * lone trailing spaces are left alone. Suspicious = contains a tab, or is
 * 3+ chars long. Space = 0, tab = 1, bits concatenated across lines. */
static void trailing(void) {
    size_t i = 0, k = 0, j, line = 1, bits = 0;
    unsigned char b[256] = {0};

    while (i < m) {
        if (out[i] == ' ' || out[i] == '\t') {
            int tab = 0;
            for (j = i; j < m && (out[j] == ' ' || out[j] == '\t'); j++)
                tab |= out[j] == '\t';
            if ((j == m || out[j] == '\n') && (tab || j - i >= 3)) {
                found++;
                fprintf(stderr, "line %zu: suspicious trailing whitespace (%zu chars)\n", line, j - i);
                for (; i < j; i++, bits++)      /* harvest bits, drop the chars */
                    if (bits / 8 < sizeof b && out[i] == '\t')
                        b[bits / 8] |= 0x80 >> (bits % 8);
                continue;
            }
            while (i < j) out[k++] = out[i++];  /* ordinary whitespace: keep */
            continue;
        }
        if (out[i] == '\n') line++;
        out[k++] = out[i++];
    }
    m = k;
    if (want_decode && bits >= 8)
        show("whitespace payload", b, bits / 8 < sizeof b ? bits / 8 : sizeof b);
}

/* ---- 9. main -------------------------------------------------------- */

int main(int argc, char **argv) {
    int check = 0;
    const char *path = NULL;
    for (int i = 1; i < argc; i++)
        if (!strcmp(argv[i], "-c")) check = 1;
        else if (!strcmp(argv[i], "-d")) want_decode = 1;
        else path = argv[i];

    FILE *f = path ? fopen(path, "rb") : stdin;
    if (!f) { perror(path); return 2; }

    /* slurp the whole input; simple, and lets every stage look ahead/behind */
    size_t cap = 1 << 16, len = 0, r;
    unsigned char *buf = malloc(cap);
    if (!buf) return 2;
    while ((r = fread(buf + len, 1, cap - len, f)) > 0) {
        len += r;
        if (len == cap && !(buf = realloc(buf, cap *= 2))) return 2;
    }

    /* every codepoint takes >= 1 byte, so len slots always suffice */
    cp  = malloc((len + 1) * sizeof *cp);
    out = malloc((len + 1) * sizeof *out);
    if (!cp || !out) return 2;
    for (size_t i = 0; i < len; ) {
        int l = dec(buf + i, len - i, &cp[n]);
        if (!l) { cp[n] = 0x110000 + buf[i]; l = 1; }   /* mark invalid byte */
        n++;
        i += l;
    }

    homoglyphs();
    strip();
    trailing();

    if (!check) for (size_t i = 0; i < m; i++) put(out[i]);
    return check && found;
}
