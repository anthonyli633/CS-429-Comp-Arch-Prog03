
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>

#define MAX_LABELS 10000
#define MAX_IMMEDIATE_SIZE 0xFFF // 12 bits for immediate values
#define MAX_LINE 1024

typedef enum {
    OP_AND    = 0x00,
    OP_OR     = 0x01,
    OP_XOR    = 0x02,
    OP_NOT    = 0x03,
    OP_SHFTR  = 0x04,
    OP_SHFTRI = 0x05,
    OP_SHFTL  = 0x06,
    OP_SHFTLI = 0x07,
    OP_BR     = 0x08,
    OP_BRR    = 0x09,   // brr rd
    OP_BRR_L  = 0x0A,   // brr L (signed PC-relative imm12)
    OP_BRNZ   = 0x0B,
    OP_CALL   = 0x0C,
    OP_RETURN = 0x0D,
    OP_BRGT   = 0x0E,
    OP_PRIV   = 0x0F,
    OP_MOV_MR = 0x10, // mov rd, (rs)(L)
    OP_MOV_RR = 0x11, // mov rd, rs
    OP_MOV_RL = 0x12, // mov rd, L (unsigned imm12)
    OP_MOV_RM = 0x13, // mov (rd)(L), rs
    OP_ADDF   = 0x14,
    OP_SUBF   = 0x15,
    OP_MULF   = 0x16,
    OP_DIVF   = 0x17,
    OP_ADD    = 0x18,
    OP_ADDI   = 0x19,
    OP_SUB    = 0x1A,
    OP_SUBI   = 0x1B,
    OP_MUL    = 0x1C,
    OP_DIV    = 0x1D
} Opcode;

typedef enum {
    FMT_RRR,    // rd, rs, rt
    FMT_RI,     // rd, L
    FMT_RR,     // rd, rs
    FMT_R,      // rd
    FMT_L,      // L
    FMT_RRL,    // rd, rs, L
    FMT_PRIV,   // rd, rs, rt, L
    FMT_NONE
} InstrFormat;

typedef struct {
    const char *name;
    InstrFormat fmt;
    Opcode opcode;
} InstrDesc;

static const InstrDesc instr_table[] = {
    { "add",    FMT_RRR, OP_ADD  },
    { "addi",   FMT_RI,  OP_ADDI },
    { "sub",    FMT_RRR, OP_SUB  },
    { "subi",   FMT_RI,  OP_SUBI },
    { "mul",    FMT_RRR, OP_MUL  },
    { "div",    FMT_RRR, OP_DIV  },
    { "and",    FMT_RRR, OP_AND  },
    { "or",     FMT_RRR, OP_OR   },
    { "xor",    FMT_RRR, OP_XOR  },
    { "not",    FMT_RR,  OP_NOT  },     // not rd, rs
    { "shftr",  FMT_RRR, OP_SHFTR  },
    { "shftri", FMT_RI,  OP_SHFTRI },   // shftri rd, L (unsigned)
    { "shftl",  FMT_RRR, OP_SHFTL  },
    { "shftli", FMT_RI,  OP_SHFTLI },   // shftli rd, L (unsigned)
    { "br",     FMT_R,   OP_BR     },
    { "brnz",   FMT_RR,  OP_BRNZ   },   // brnz rd, rs  (per your original)
    { "call",   FMT_R,   OP_CALL   },
    { "return", FMT_NONE, OP_RETURN },
    { "brgt",   FMT_RRR, OP_BRGT   },
    { "priv",   FMT_PRIV, OP_PRIV  },
    { "addf",   FMT_RRR, OP_ADDF },
    { "subf",   FMT_RRR, OP_SUBF },
    { "mulf",   FMT_RRR, OP_MULF },
    { "divf",   FMT_RRR, OP_DIVF },
    { NULL,     0,       0},
};

typedef struct {
    char name[256];
    uint64_t addr;
} Label;

static Label labels[MAX_LABELS];
static int label_count = 0;

static void dief(const char *msg, const char *line) {
    if (line) fprintf(stderr, "%s: %s\n", msg, line);
    else fprintf(stderr, "%s\n", msg);
    exit(1);
}

static int is_valid_label_name(const char *s) {
    if (!s || !*s) return 0;
    if (!(isalpha((unsigned char)s[0]) || s[0] == '_')) return 0;
    for (int i = 1; s[i]; i++) {
        if (!(isalnum((unsigned char)s[i]) || s[i] == '_')) return 0;
    }
    return 1;
}

static int find_label_index(const char *name) {
    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, name) == 0) return i;
    }
    return -1;
}

static uint64_t get_addr(const char *label) {
    int idx = find_label_index(label);
    if (idx < 0) return (uint64_t)-1;
    return labels[idx].addr;
}

static void add_label_checked(const char *name, uint64_t addr) {
    if (!is_valid_label_name(name)) dief("Invalid label name", name);
    if (label_count >= MAX_LABELS) dief("Too many labels", NULL);
    if (find_label_index(name) >= 0) dief("Duplicate label", name);

    strncpy(labels[label_count].name, name, sizeof(labels[label_count].name) - 1);
    labels[label_count].name[sizeof(labels[label_count].name) - 1] = '\0';
    labels[label_count].addr = addr;
    label_count++;
}

static void trim_comment_and_trailing_ws(char *line) {
    char *semi = strchr(line, ';');
    if (semi) *semi = '\0';
    size_t n = strlen(line);
    while (n > 0 && isspace((unsigned char)line[n - 1])) line[--n] = '\0';
}

static int line_has_non_ws(const char *s) {
    for (int i = 0; s[i]; i++) {
        if (!isspace((unsigned char)s[i])) return 1;
    }
    return 0;
}

static void enforce_no_leading_spaces(const char *raw_line) {
    if (raw_line && raw_line[0] == ' ') {
        dief("Leading spaces are invalid (statements must start with a tab)", raw_line);
    }
}

static void enforce_tab_rule_if_statement(const char *raw_line, const char *trimmed_ptr) {
    if (!trimmed_ptr || *trimmed_ptr == '\0') return;
    if (strncmp(trimmed_ptr, ".code", 5) == 0) return;
    if (strncmp(trimmed_ptr, ".data", 5) == 0) return;
    if (*trimmed_ptr == ':') return;

    if (!raw_line || raw_line[0] != '\t') {
        dief("Statement line must begin with a tab", raw_line);
    }
}

static void enforce_label_only(const char *ptr) {
    // ptr points to ':' in the trimmed line (comments already removed)
    const char *p = ptr + 1;
    if (!(isalpha((unsigned char)*p) || *p == '_')) dief("Invalid label name", ptr);
    p++;
    while (isalnum((unsigned char)*p) || *p == '_') p++;
    while (*p) {
        if (!isspace((unsigned char)*p)) dief("Label must be alone on its line", ptr);
        p++;
    }
}

// token parser: uses spaces, commas, tabs as separators
static char *my_strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *p = (char *)malloc(len);
    if (p) memcpy(p, s, len);
    return p;
}

static char *parse_token(char **p) {
    while (**p && (isspace((unsigned char)**p) || **p == ',')) (*p)++;
    if (**p == '\0') return NULL;
    char buf[512];
    int i = 0;
    while (**p && !isspace((unsigned char)**p) && **p != ',') {
        if (i < (int)sizeof(buf) - 1) buf[i++] = **p;
        (*p)++;
    }
    buf[i] = '\0';
    return my_strdup(buf);
}

static bool parse_u64_decimal_or_label(const char *tok, uint64_t *out) {
    if (!tok || !*tok) return false;

    // optional u/U suffix (like working code)
    char tmp[512];
    strncpy(tmp, tok, sizeof(tmp) - 1);
    tmp[sizeof(tmp) - 1] = '\0';
    size_t n = strlen(tmp);
    while (n && isspace((unsigned char)tmp[n - 1])) tmp[--n] = '\0';

    if (tmp[0] == ':') {
        if (!is_valid_label_name(tmp + 1)) return false;
        uint64_t addr = get_addr(tmp + 1);
        if (addr == (uint64_t)-1) return false;
        *out = addr;
        return true;
    }

    if (tmp[0] == '-') return false;

    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(tmp, &end, 10);
    if (errno == ERANGE) return false;
    if (!end || *end != '\0') return false;
    *out = (uint64_t)v;
    return true;
}

// general int64 (for branch offsets / mem offsets). base 0 allowed.
static bool parse_i64_literal(const char *s, int64_t *out) {
    if (!s || !*s) return false;
    errno = 0;
    char *end = NULL;
    long long v = strtoll(s, &end, 0);
    if (errno != 0) return false;
    if (!end || *end != '\0') return false;
    *out = (int64_t)v;
    return true;
}

static bool parse_u64_literal_base0_unsigned(const char *s, uint64_t *out) {
    if (!s || !*s) return false;
    if (s[0] == ':') return false;
    if (s[0] == '-') return false;

    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 0);
    if (errno != 0) return false;
    if (!end || *end != '\0') return false;
    *out = (uint64_t)v;
    return true;
}
static bool resolve_i64_value(const char *tok, int64_t *out) {
    if (!tok || !*tok) return false;
    if (tok[0] == ':') {
        if (!is_valid_label_name(tok + 1)) return false;
        uint64_t addr = get_addr(tok + 1);
        if (addr == (uint64_t)-1) return false;
        // absolute address may exceed int64, but our program addresses start at 0x1000 so ok
        *out = (int64_t)addr;
        return true;
    }
    return parse_i64_literal(tok, out);
}

static bool parse_mem_operand(const char *tok, uint8_t *base, int64_t *off) {
    if (!tok || !base || !off) return false;
    const char *p = tok;
    if (*p != '(') return false;
    p++;
    if (*p != 'r') return false;
    p++;

    errno = 0;
    char *end = NULL;
    long reg = strtol(p, &end, 10);
    if (errno != 0 || end == p || *end != ')' || reg < 0 || reg > 31) return false;
    *base = (uint8_t)reg;

    p = end + 1;
    if (*p != '(') return false;
    p++;

    errno = 0;
    long long offset = strtoll(p, &end, 0);
    if (errno != 0 || end == p || *end != ')') return false;

    p = end + 1;
    if (*p != '\0') return false;

    *off = (int64_t)offset;
    return true;
}

static uint32_t imm12_signed(int64_t x) {
    if (x < -2048 || x > 2047) return 0xFFFFFFFFu;
    return (uint32_t)(x & 0xFFF);
}

static uint32_t imm12_unsigned(uint64_t x) {
    if (x > 0xFFFULL) return 0xFFFFFFFFu;
    return (uint32_t)(x & 0xFFF);
}

static void clr(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\txor %s, %s, %s\n", rd, rd, rd);
}
static void in_(FILE *intermediate, const char *rd, const char *rs) {
    fprintf(intermediate, "\tpriv %s, %s, r0, 3\n", rd, rs);
}
static void out_(FILE *intermediate, const char *rd, const char *rs) {
    fprintf(intermediate, "\tpriv %s, %s, r0, 4\n", rd, rs);
}
static void push(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\tmov (r31)(-8), %s\n", rd);
    fprintf(intermediate, "\tsubi r31, 8\n");
}
static void pop(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\tmov %s, (r31)(0)\n", rd);
    fprintf(intermediate, "\taddi r31, 8\n");
}
static void halt(FILE *intermediate) {
    fprintf(intermediate, "\tpriv r0, r0, r0, 0\n");
}
static void ld(FILE *intermediate, const char *rd, uint64_t L) {
    fprintf(intermediate, "\txor %s, %s, %s\n", rd, rd, rd);
    fprintf(intermediate, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 52) & 0xFFFULL));
    fprintf(intermediate, "\tshftli %s, 12\n", rd);
    fprintf(intermediate, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 40) & 0xFFFULL));
    fprintf(intermediate, "\tshftli %s, 12\n", rd);
    fprintf(intermediate, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 28) & 0xFFFULL));
    fprintf(intermediate, "\tshftli %s, 12\n", rd);
    fprintf(intermediate, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 16) & 0xFFFULL));
    fprintf(intermediate, "\tshftli %s, 12\n", rd);
    fprintf(intermediate, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 4) & 0xFFFULL));
    fprintf(intermediate, "\tshftli %s, 4\n", rd);
    fprintf(intermediate, "\taddi %s, %llu\n", rd, (unsigned long long)(L & 0xFULL));
}

void parseInput(FILE *input) {
    char raw[MAX_LINE];

    int section = -1; // 0 code, 1 data
    uint64_t pc = 0x1000;

    while (fgets(raw, sizeof(raw), input)) {
        enforce_no_leading_spaces(raw);

        char line[MAX_LINE];
        strcpy(line, raw);
        trim_comment_and_trailing_ws(line);
        if (!line_has_non_ws(line)) continue;

        // ptr to first non-ws in trimmed line
        char *ptr = line;
        while (isspace((unsigned char)*ptr)) ptr++;
        if (*ptr == '\0') continue;

        // section directives
        if (strncmp(ptr, ".code", 5) == 0 && (ptr[5] == '\0' || isspace((unsigned char)ptr[5]))) {
            // must be only ".code" (after comment removal)
            // allow whitespace only after .code
            char *q = ptr + 5;
            while (*q) { if (!isspace((unsigned char)*q)) dief("Unknown section directive", raw); q++; }
            section = 0;
            continue;
        }
        if (strncmp(ptr, ".data", 5) == 0 && (ptr[5] == '\0' || isspace((unsigned char)ptr[5]))) {
            char *q = ptr + 5;
            while (*q) { if (!isspace((unsigned char)*q)) dief("Unknown section directive", raw); q++; }
            section = 1;
            continue;
        }

        // labels
        if (*ptr == ':') {
            enforce_label_only(ptr);

            char label_name[256];
            // read token after ':'
            const char *p = ptr + 1;
            int i = 0;
            while (*p && !isspace((unsigned char)*p) && i < (int)sizeof(label_name) - 1) {
                label_name[i++] = *p++;
            }
            label_name[i] = '\0';

            add_label_checked(label_name, pc);
            continue;
        }

        enforce_tab_rule_if_statement(raw, ptr);

        if (section == -1) dief("Instruction/data outside of .code/.data", raw);

        if (section == 0) {
            char tmp[MAX_LINE];
            strcpy(tmp, ptr);
            // tokenize (first token is mnemonic)
            char *tp = tmp;
            char *mnem = parse_token(&tp);
            if (!mnem) dief("Malformed instruction", raw);

            int num_instructions = 1;
            if (strcmp(mnem, "push") == 0) num_instructions = 2;
            else if (strcmp(mnem, "pop") == 0) num_instructions = 2;
            else if (strcmp(mnem, "ld") == 0) num_instructions = 12;

            pc += 4ULL * (uint64_t)num_instructions;
            free(mnem);
        } else {
            // data: must be non-negative, in 64-bit range, decimal-only (or :label), no extra tokens
            char *tp = ptr;
            char *tok = parse_token(&tp);
            if (!tok) dief("Malformed data line", raw);

            uint64_t v;
            if (!parse_u64_decimal_or_label(tok, &v)) {
                free(tok);
                dief("Invalid data literal (must be unsigned decimal in 64-bit range, or :label)", raw);
            }
            free(tok);

            char *extra = parse_token(&tp);
            if (extra) {
                free(extra);
                dief("Extra token in data line", raw);
            }
            pc += 8ULL;
        }
    }
}

// ===================== Pass 1b: generate intermediate (macros expanded) =====================

void generateIntermediate(FILE *input, FILE *intermediate) {
    char raw[MAX_LINE];
    int section = -1; // 0 code, 1 data
    int last_section_written = -1;

    // Track PC for brr :label to emit signed instruction-count offsets
    uint64_t pc = 0x1000;

    while (fgets(raw, sizeof(raw), input)) {
        enforce_no_leading_spaces(raw);

        char line[MAX_LINE];
        strcpy(line, raw);
        trim_comment_and_trailing_ws(line);
        if (!line_has_non_ws(line)) continue;

        char *ptr = line;
        while (isspace((unsigned char)*ptr)) ptr++;
        if (*ptr == '\0') continue;

        if (strncmp(ptr, ".code", 5) == 0) {
            section = 0;
            if (last_section_written != 0) {
                fprintf(intermediate, ".code\n");
                last_section_written = 0;
            }
            continue;
        }
        if (strncmp(ptr, ".data", 5) == 0) {
            section = 1;
            if (last_section_written != 1) {
                fprintf(intermediate, ".data\n");
                last_section_written = 1;
            }
            continue;
        }

        if (*ptr == ':') {
            // label line - do not emit in intermediate
            continue;
        }

        enforce_tab_rule_if_statement(raw, ptr);

        if (section == -1) dief("Statement outside of .code/.data", raw);

        if (section == 1) {
            // data: validate and emit normalized decimal
            uint64_t v;
            if (!parse_u64_decimal_or_label(ptr, &v)) dief("Invalid data line", raw);
            fprintf(intermediate, "\t%llu\n", (unsigned long long)v);
            pc += 8ULL;
            continue;
        }

        // code
        char *p = ptr;
        char *instr = parse_token(&p);
        if (!instr) continue;

        if (strcmp(instr, "clr") == 0) {
            char *rd = parse_token(&p);
            char *extra = parse_token(&p);
            if (!rd || extra) dief("Malformed clr", raw);
            clr(intermediate, rd);
            free(rd); free(extra); free(instr);
            pc += 4ULL;
            continue;
        }
        if (strcmp(instr, "in") == 0) {
            char *rd = parse_token(&p);
            char *rs = parse_token(&p);
            char *extra = parse_token(&p);
            if (!rd || !rs || extra) dief("Malformed in", raw);
            in_(intermediate, rd, rs);
            free(rd); free(rs); free(extra); free(instr);
            pc += 4ULL;
            continue;
        }
        if (strcmp(instr, "out") == 0) {
            char *rd = parse_token(&p);
            char *rs = parse_token(&p);
            char *extra = parse_token(&p);
            if (!rd || !rs || extra) dief("Malformed out", raw);
            out_(intermediate, rd, rs);
            free(rd); free(rs); free(extra); free(instr);
            pc += 4ULL;
            continue;
        }
        if (strcmp(instr, "push") == 0) {
            char *rd = parse_token(&p);
            char *extra = parse_token(&p);
            if (!rd || extra) dief("Malformed push", raw);
            push(intermediate, rd);
            free(rd); free(extra); free(instr);
            pc += 8ULL;
            continue;
        }
        if (strcmp(instr, "pop") == 0) {
            char *rd = parse_token(&p);
            char *extra = parse_token(&p);
            if (!rd || extra) dief("Malformed pop", raw);
            pop(intermediate, rd);
            free(rd); free(extra); free(instr);
            pc += 8ULL;
            continue;
        }
        if (strcmp(instr, "halt") == 0) {
            char *extra = parse_token(&p);
            if (extra) dief("Malformed halt", raw);
            halt(intermediate);
            free(extra); free(instr);
            pc += 4ULL;
            continue;
        }
        if (strcmp(instr, "ld") == 0) {
            char *rd = parse_token(&p);
            char *Ltok = parse_token(&p);
            char *extra = parse_token(&p);
            if (!rd || !Ltok || extra) dief("Malformed ld", raw);

            uint64_t L;
            if (Ltok[0] == ':') {
                if (!is_valid_label_name(Ltok + 1)) dief("Invalid label in ld", raw);
                L = get_addr(Ltok + 1);
                if (L == (uint64_t)-1) dief("Unknown label in ld", raw);
            } else {
                if (!parse_u64_literal_base0_unsigned(Ltok, &L)) dief("Invalid literal in ld", raw);
            }

            ld(intermediate, rd, L);
            free(rd); free(Ltok); free(extra); free(instr);
            pc += 48ULL;
            continue;
        }

        if (strcmp(instr, "brr") == 0) {
            char *arg = parse_token(&p);
            char *extra = parse_token(&p);
            if (!arg || extra) dief("Malformed brr", raw);

            if (arg[0] == ':') {
                if (!is_valid_label_name(arg + 1)) dief("Invalid label in brr", raw);
                uint64_t target = get_addr(arg + 1);
                if (target == (uint64_t)-1) dief("Unknown label in brr", raw);

                // PC-relative offset in instructions: (target - (pc + 4)) / 4
                int64_t diff_bytes = (int64_t)target - (int64_t)(pc + 4ULL);
                int64_t L_inst = diff_bytes / 4LL;
                fprintf(intermediate, "\tbrr %lld\n", (long long)L_inst);
            } else {
                fprintf(intermediate, "\tbrr %s\n", arg);
            }

            free(arg); free(extra); free(instr);
            pc += 4ULL;
            continue;
        }

        fprintf(intermediate, "\t%s", instr);
        free(instr);

        char *tok = parse_token(&p);
        int first = 1;
        while (tok) {
            fprintf(intermediate, "%s%s", (first ? " " : ", "), tok);
            first = 0;
            free(tok);
            tok = parse_token(&p);
        }
        fprintf(intermediate, "\n");
        pc += 4ULL;
    }
}

static void write_u32(FILE *out, uint32_t w) { fwrite(&w, sizeof(w), 1, out); }
static void write_u64(FILE *out, uint64_t x) { fwrite(&x, sizeof(x), 1, out); }

static void write_instr(FILE *out, Opcode opcode,
                        uint8_t rd, uint8_t rs, uint8_t rt,
                        uint32_t imm12) {
    if (opcode > 0x1F) dief("Opcode out of 5-bit range", NULL);
    if (rd > 31 || rs > 31 || rt > 31) dief("Register out of range", NULL);
    if (imm12 > 0xFFF) dief("Immediate out of 12-bit range", NULL);

    uint32_t inst = 0;
    inst |= ((uint32_t)opcode & 0x1F) << 27;
    inst |= ((uint32_t)rd     & 0x1F) << 22;
    inst |= ((uint32_t)rs     & 0x1F) << 17;
    inst |= ((uint32_t)rt     & 0x1F) << 12;
    inst |= ((uint32_t)imm12  & 0xFFF);

    write_u32(out, inst);
}

static const char *valid_registers[] = {
    "r0","r1","r2","r3","r4","r5","r6","r7",
    "r8","r9","r10","r11","r12","r13","r14","r15",
    "r16","r17","r18","r19","r20","r21","r22","r23",
    "r24","r25","r26","r27","r28","r29","r30","r31"
};

static bool parse_reg_num(const char *tok, uint8_t *out) {
    for (int i = 0; i < 32; i++) {
        if (strcmp(tok, valid_registers[i]) == 0) {
            *out = (uint8_t)i;
            return true;
        }
    }
    return false;
}

static void clearFile(const char *path) {
    FILE *f = fopen(path, "w");
    if (f) fclose(f);
}

bool generateOutput(FILE *intermediate, FILE *output) {
    char raw[MAX_LINE];
    int section = -1; // 0 code, 1 data

    while (fgets(raw, sizeof(raw), intermediate)) {
        // intermediate must already be clean, but still strip comments/trailing ws
        char line[MAX_LINE];
        strcpy(line, raw);
        trim_comment_and_trailing_ws(line);
        if (!line_has_non_ws(line)) continue;

        char *ptr = line;
        while (isspace((unsigned char)*ptr)) ptr++;
        if (*ptr == '\0') continue;

        if (strncmp(ptr, ".code", 5) == 0) { section = 0; continue; }
        if (strncmp(ptr, ".data", 5) == 0) { section = 1; continue; }

        // Statements must begin with tab in intermediate
        if (raw[0] != '\t') dief("Intermediate invalid: statement missing leading tab", raw);
        if (section == -1) dief("Content outside section", raw);

        if (section == 1) {
            // .data: strict decimal/label, non-negative, in 64-bit range
            uint64_t v;
            if (!parse_u64_decimal_or_label(ptr, &v)) dief("Bad data literal in intermediate", raw);
            write_u64(output, v);
            continue;
        }

        // code
        char *p = ptr;
        char *op = parse_token(&p);
        if (!op) continue;

        // mov special handling (same as your original, but keep checks)
        if (strcmp(op, "mov") == 0) {
            char *t1 = parse_token(&p);
            char *t2 = parse_token(&p);
            char *t3 = parse_token(&p);
            if (!t1 || !t2 || t3) {
                free(op); free(t1); free(t2); free(t3);
                dief("Invalid mov instruction", raw);
            }

            uint8_t rd, rs;
            uint64_t uimm;

            // mov rd, rs
            if (parse_reg_num(t1, &rd) && parse_reg_num(t2, &rs)) {
                write_instr(output, OP_MOV_RR, rd, rs, 0, 0);
            }
            // mov rd, L (unsigned imm12)
            else if (parse_reg_num(t1, &rd) && parse_u64_literal_base0_unsigned(t2, &uimm)) {
                uint32_t imm12 = imm12_unsigned(uimm);
                if (imm12 == 0xFFFFFFFFu) dief("Immediate too large for mov rd, L", raw);
                write_instr(output, OP_MOV_RL, rd, 0, 0, imm12);
            }
            // mov rd, (rs)(L)   (load)
            else if (parse_reg_num(t1, &rd) && t2[0] == '(') {
                uint8_t base;
                int64_t off;
                if (!parse_mem_operand(t2, &base, &off)) dief("Invalid memory operand for mov rd,(rs)(L)", raw);
                uint32_t imm12 = imm12_signed(off);
                if (imm12 == 0xFFFFFFFFu) dief("mov offset out of signed 12-bit range", raw);
                write_instr(output, OP_MOV_MR, rd, base, 0, imm12);
            }
            // mov (rd)(L), rs   (store)
            else if (t1[0] == '(' && parse_reg_num(t2, &rs)) {
                uint8_t base;
                int64_t off;
                if (!parse_mem_operand(t1, &base, &off)) dief("Invalid memory operand for mov (rd)(L),rs", raw);
                uint32_t imm12 = imm12_signed(off);
                if (imm12 == 0xFFFFFFFFu) dief("mov offset out of signed 12-bit range", raw);
                write_instr(output, OP_MOV_RM, base, rs, 0, imm12);
            }
            else {
                free(op); free(t1); free(t2);
                dief("Invalid mov operands", raw);
            }

            free(op); free(t1); free(t2);
            continue;
        }

        // brr special handling:
        // - brr rd -> OP_BRR
        // - brr L  -> OP_BRR_L with signed imm12 (PC-relative count already computed in intermediate if label)
        if (strcmp(op, "brr") == 0) {
            char *t1 = parse_token(&p);
            char *t2 = parse_token(&p);
            if (!t1 || t2) {
                free(op); free(t1); free(t2);
                dief("Invalid arguments for brr", raw);
            }

            uint8_t rd;
            if (parse_reg_num(t1, &rd)) {
                write_instr(output, OP_BRR, rd, 0, 0, 0);
            } else {
                int64_t L;
                // intermediate should have numeric for labels already; but accept numeric token
                if (!parse_i64_literal(t1, &L)) {
                    free(op); free(t1);
                    dief("Invalid brr literal (must be signed int)", raw);
                }
                uint32_t imm12 = imm12_signed(L);
                if (imm12 == 0xFFFFFFFFu) dief("brr offset out of signed 12-bit range", raw);
                write_instr(output, OP_BRR_L, 0, 0, 0, imm12);
            }

            free(op); free(t1);
            continue;
        }

        // Look up opcode/format
        const InstrDesc *desc = NULL;
        for (int i = 0; instr_table[i].name; i++) {
            if (strcmp(op, instr_table[i].name) == 0) { desc = &instr_table[i]; break; }
        }
        if (!desc) {
            free(op);
            dief("Unknown instruction in intermediate", raw);
        }

        char *t1 = parse_token(&p);
        char *t2 = parse_token(&p);
        char *t3 = parse_token(&p);
        char *t4 = parse_token(&p);
        char *t5 = parse_token(&p);

        if (desc->fmt == FMT_RRR) {
            uint8_t rd, rs, rt;
            if (!t1 || !t2 || !t3 || t4) dief("Bad RRR format", raw);
            if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs) || !parse_reg_num(t3, &rt))
                dief("Bad RRR operands", raw);
            write_instr(output, desc->opcode, rd, rs, rt, 0);
        }
        else if (desc->fmt == FMT_RI) {
            uint8_t rd;
            uint64_t uimm;
            if (!t1 || !t2 || t3) dief("Bad RI format", raw);
            if (!parse_reg_num(t1, &rd)) dief("Bad RI register", raw);
            if (t2[0] == ':') {
                if (!is_valid_label_name(t2 + 1)) dief("Invalid label", raw);
                uint64_t addr = get_addr(t2 + 1);
                if (addr == (uint64_t)-1) dief("Unknown label", raw);
                uimm = addr;
            } else {
                if (!parse_u64_literal_base0_unsigned(t2, &uimm)) dief("Bad RI immediate", raw);
            }

            uint32_t imm12 = imm12_unsigned(uimm);
            if (imm12 == 0xFFFFFFFFu) dief("RI immediate out of 12-bit unsigned range", raw);
            write_instr(output, desc->opcode, rd, 0, 0, imm12);
        }
        else if (desc->fmt == FMT_RR) {
            uint8_t rd, rs;
            if (!t1 || !t2 || t3) dief("Bad RR format", raw);
            if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs)) dief("Bad RR operands", raw);
            write_instr(output, desc->opcode, rd, rs, 0, 0);
        }
        else if (desc->fmt == FMT_R) {
            uint8_t rd;
            if (!t1 || t2) dief("Bad R format", raw);
            if (!parse_reg_num(t1, &rd)) dief("Bad R operand", raw);
            write_instr(output, desc->opcode, rd, 0, 0, 0);
        }
        else if (desc->fmt == FMT_L) {
            // unsigned imm12
            uint64_t uimm;
            if (!t1 || t2) dief("Bad L format", raw);

            if (t1[0] == ':') {
                if (!is_valid_label_name(t1 + 1)) dief("Invalid label", raw);
                uint64_t addr = get_addr(t1 + 1);
                if (addr == (uint64_t)-1) dief("Unknown label", raw);
                uimm = addr;
            } else {
                if (!parse_u64_literal_base0_unsigned(t1, &uimm)) dief("Bad L operand", raw);
            }

            uint32_t imm12 = imm12_unsigned(uimm);
            if (imm12 == 0xFFFFFFFFu) dief("L immediate out of 12-bit unsigned range", raw);
            write_instr(output, desc->opcode, 0, 0, 0, imm12);
        }
        else if (desc->fmt == FMT_RRL) {
            // rd, rs, unsigned imm12 (or label)
            uint8_t rd, rs;
            uint64_t uimm;
            if (!t1 || !t2 || !t3 || t4) dief("Bad RRL format", raw);
            if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs)) dief("Bad RRL regs", raw);

            if (t3[0] == ':') {
                if (!is_valid_label_name(t3 + 1)) dief("Invalid label", raw);
                uint64_t addr = get_addr(t3 + 1);
                if (addr == (uint64_t)-1) dief("Unknown label", raw);
                uimm = addr;
            } else {
                if (!parse_u64_literal_base0_unsigned(t3, &uimm)) dief("Bad RRL immediate", raw);
            }

            uint32_t imm12 = imm12_unsigned(uimm);
            if (imm12 == 0xFFFFFFFFu) dief("RRL immediate out of 12-bit unsigned range", raw);
            write_instr(output, desc->opcode, rd, rs, 0, imm12);
        }
        else if (desc->fmt == FMT_PRIV) {
            uint8_t rd, rs, rt;
            uint64_t uimm;
            if (!t1 || !t2 || !t3 || !t4 || t5) dief("Bad PRIV format", raw);
            if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs) || !parse_reg_num(t3, &rt))
                dief("Bad PRIV regs", raw);

            if (t4[0] == ':') {
                if (!is_valid_label_name(t4 + 1)) dief("Invalid label", raw);
                uint64_t addr = get_addr(t4 + 1);
                if (addr == (uint64_t)-1) dief("Unknown label", raw);
                uimm = addr;
            } else {
                if (!parse_u64_literal_base0_unsigned(t4, &uimm)) dief("Bad PRIV immediate", raw);
            }

            uint32_t imm12 = imm12_unsigned(uimm);
            if (imm12 == 0xFFFFFFFFu) dief("PRIV immediate out of 12-bit unsigned range", raw);
            write_instr(output, desc->opcode, rd, rs, rt, imm12);
        }
        else if (desc->fmt == FMT_NONE) {
            if (t1) dief("Unexpected operand for no-operand instruction", raw);
            write_instr(output, desc->opcode, 0, 0, 0, 0);
        }
        else {
            dief("Unhandled format in Stage 2", raw);
        }

        free(op);
        free(t1); free(t2); free(t3); free(t4); free(t5);
    }

    return true;
}

int main(int argc, char *argv[]) {
    if (argc != 4) {
        fprintf(stderr, "Incorrect number of arguments\n");
        return 1;
    }

    FILE *input = fopen(argv[1], "r");
    FILE *intermediate = fopen(argv[2], "w");
    FILE *output = fopen(argv[3], "wb");

    if (!input || !intermediate || !output) {
        fprintf(stderr, "Could not open input, intermediate, or output file\n");
        if (input) fclose(input);
        if (intermediate) fclose(intermediate);
        if (output) fclose(output);
        return 1;
    }

    // pass 1: labels + size checking
    parseInput(input);

    // pass 1b: write intermediate
    rewind(input);
    generateIntermediate(input, intermediate);

    fclose(input);
    fclose(intermediate);

    // pass 2: generate binary
    FILE *intermediate2 = fopen(argv[2], "r");
    if (!intermediate2) {
        fprintf(stderr, "Could not open intermediate for reading\n");
        fclose(output);
        return 1;
    }

    if (!generateOutput(intermediate2, output)) {
        fclose(intermediate2);
        fclose(output);
        clearFile(argv[2]);
        return 1;
    }

    fclose(intermediate2);
    fclose(output);
    return 0;
}