#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>

#define MAX_LABELS 1024
#define MAX_LINE   1024
#define MAX_LABEL_NAME 64
#define MAX_IMMEDIATE_U12 0xFFF

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
    OP_BRR_L  = 0x0A,   // brr L (signed 12-bit instruction offset)
    OP_BRNZ   = 0x0B,
    OP_CALL   = 0x0C,
    OP_RETURN = 0x0D,
    OP_BRGT   = 0x0E,
    OP_PRIV   = 0x0F,
    OP_MOV_MR = 0x10, // mov rd, (rs)(L)
    OP_MOV_RR = 0x11, // mov rd, rs
    OP_MOV_RL = 0x12, // mov rd, L
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
    FMT_RRR,   // rd, rs, rt
    FMT_RI,    // rd, L
    FMT_RR,    // rd, rs
    FMT_R,     // rd
    FMT_L,     // L
    FMT_RRL,   // rd, rs, L
    FMT_PRIV,  // rd, rs, rt, L
    FMT_NONE   // no operands
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
    { "not",    FMT_RR,  OP_NOT  },
    { "shftr",  FMT_RRR, OP_SHFTR  },
    { "shftri", FMT_RI,  OP_SHFTRI },
    { "shftl",  FMT_RRR, OP_SHFTL  },
    { "shftli", FMT_RI,  OP_SHFTLI },
    { "br",     FMT_R,   OP_BR     },
    { "brnz",   FMT_RR,  OP_BRNZ   },
    { "call",   FMT_R,   OP_CALL   },
    { "return", FMT_NONE,OP_RETURN },
    { "brgt",   FMT_RRR, OP_BRGT   },
    { "priv",   FMT_PRIV,OP_PRIV   },
    { "addf",   FMT_RRR, OP_ADDF },
    { "subf",   FMT_RRR, OP_SUBF },
    { "mulf",   FMT_RRR, OP_MULF },
    { "divf",   FMT_RRR, OP_DIVF },
    { NULL,     0,       0}
};

static void dief(const char *msg, const char *line) {
    if (line) fprintf(stderr, "Error: %s\nLine: %s\n", msg, line);
    else      fprintf(stderr, "Error: %s\n", msg);
    exit(1);
}

typedef struct {
    char name[MAX_LABEL_NAME];
    uint64_t addr;
} Label;

static Label labels[MAX_LABELS];
static int label_count = 0;

static int is_valid_label_name(const char *s) {
    if (!s || !*s) return 0;
    if (!(isalpha((unsigned char)s[0]) || s[0] == '_')) return 0;
    for (int i = 1; s[i]; i++) {
        if (!(isalnum((unsigned char)s[i]) || s[i] == '_')) return 0;
    }
    return 1;
}

static uint64_t get_addr(const char *label) {
    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, label) == 0) return labels[i].addr;
    }
    return (uint64_t)-1;
}

static void add_label(const char *name, uint64_t addr, const char *raw_line) {
    if (!is_valid_label_name(name)) dief("Invalid label name", raw_line);
    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, name) == 0) dief("Duplicate label", raw_line);
    }
    if (label_count >= MAX_LABELS) dief("Too many labels", raw_line);

    strncpy(labels[label_count].name, name, MAX_LABEL_NAME - 1);
    labels[label_count].name[MAX_LABEL_NAME - 1] = '\0';
    labels[label_count].addr = addr;
    label_count++;
}

static void trim_line_inplace(char *line) {
    // remove comment starting at ';'
    char *c = strchr(line, ';');
    if (c) *c = '\0';

    // strip trailing whitespace
    size_t n = strlen(line);
    while (n > 0 && isspace((unsigned char)line[n - 1])) {
        line[--n] = '\0';
    }
}

static int line_has_non_ws(const char *s) {
    for (int i = 0; s[i]; i++) if (!isspace((unsigned char)s[i])) return 1;
    return 0;
}

static void enforce_leading_space_rule(const char *raw_line) {
    if (raw_line && raw_line[0] == ' ') {
        dief("Leading spaces are invalid (must start with tab for statements)", raw_line);
    }
}

static void enforce_tab_rule_if_statement(const char *raw_line, const char *ptr_trimmed) {
    if (!ptr_trimmed || *ptr_trimmed == '\0') return;
    if (strncmp(ptr_trimmed, ".code", 5) == 0) return;
    if (strncmp(ptr_trimmed, ".data", 5) == 0) return;
    if (*ptr_trimmed == ':') return;

    if (raw_line[0] != '\t') {
        dief("Statement line must begin with a tab", raw_line);
    }
}

static void enforce_label_only(const char *trimmed_ptr, const char *raw_line) {
    // trimmed_ptr points at ':'
    const char *p = trimmed_ptr + 1;
    if (!(isalpha((unsigned char)*p) || *p == '_')) dief("Invalid label name", raw_line);
    p++;
    while (isalnum((unsigned char)*p) || *p == '_') p++;

    // after label token, only whitespace allowed
    while (*p) {
        if (!isspace((unsigned char)*p)) dief("Label must be alone on its line", raw_line);
        p++;
    }
}

static char *my_strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *p = (char*)malloc(len);
    if (!p) return NULL;
    memcpy(p, s, len);
    return p;
}

static char* parse_token(char **p) {
    while (**p && (isspace((unsigned char)**p) || **p == ',')) (*p)++;
    if (**p == '\0') return NULL;

    char token[256];
    int i = 0;
    while (**p && !isspace((unsigned char)**p) && **p != ',') {
        if (i < (int)sizeof(token) - 1) token[i++] = **p;
        (*p)++;
    }
    token[i] = '\0';
    return my_strdup(token);
}

static bool parse_u64_anybase_strict(const char *s, uint64_t *out) {
    if (!s || !*s) return false;
    if (s[0] == ':') return false;
    if (s[0] == '-') return false;

    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 0);
    if (errno == ERANGE) return false;
    if (errno != 0) return false;
    if (!end || end == s || *end != '\0') return false;

    *out = (uint64_t)v;
    return true;
}

// For .data lines: strict unsigned decimal, 0 <= v <= UINT64_MAX
static bool parse_u64_decimal_strict(const char *s, uint64_t *out) {
    if (!s || !*s) return false;
    if (s[0] == '-') return false;
    if (s[0] == ':') return false; // data must be literal

    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 10);
    if (errno == ERANGE) return false;
    if (errno != 0) return false;
    if (!end || end == s || *end != '\0') return false;

    *out = (uint64_t)v;
    return true;
}

static uint32_t imm12_signed_pack(int64_t x) {
    if (x < -2048 || x > 2047) return 0xFFFFFFFFu;
    return (uint32_t)(x & 0xFFF);
}

// -------------------- Register / mem parsing --------------------

static const char* valid_registers[] = {
    "r0","r1","r2","r3","r4","r5","r6","r7",
    "r8","r9","r10","r11","r12","r13","r14","r15",
    "r16","r17","r18","r19","r20","r21","r22","r23",
    "r24","r25","r26","r27","r28","r29","r30","r31"
};

static bool parse_reg_num(const char *tok, uint8_t *out) {
    if (!tok || !out) return false;
    for (int i = 0; i < 32; i++) {
        if (strcmp(tok, valid_registers[i]) == 0) {
            *out = (uint8_t)i;
            return true;
        }
    }
    return false;
}

static bool parse_mem_operand(const char *tok, uint8_t *base, int64_t *off) {
    if (!tok || !base || !off) return false;
    const char *p = tok;
    if (*p != '(') return false;
    p++;
    if (*p != 'r') return false;
    p++;

    char *end = NULL;
    errno = 0;
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

static void m_clr(FILE *out, const char *rd) {
    fprintf(out, "\txor %s, %s, %s\n", rd, rd, rd);
}
static void m_in(FILE *out, const char *rd, const char *rs) {
    fprintf(out, "\tpriv %s, %s, r0, 3\n", rd, rs);
}
static void m_out(FILE *out, const char *rd, const char *rs) {
    fprintf(out, "\tpriv %s, %s, r0, 4\n", rd, rs);
}
static void m_push(FILE *out, const char *rd) {
    fprintf(out, "\tmov (r31)(-8), %s\n", rd);
    fprintf(out, "\tsubi r31, 8\n");
}
static void m_pop(FILE *out, const char *rd) {
    fprintf(out, "\tmov %s, (r31)(0)\n", rd);
    fprintf(out, "\taddi r31, 8\n");
}
static void m_halt(FILE *out) {
    fprintf(out, "\tpriv r0, r0, r0, 0\n");
}

// Expands a 64-bit constant using addi/shftli sequence (12 instructions total = 48 bytes)
static void m_ld(FILE *out, const char *rd, uint64_t L) {
    fprintf(out, "\txor %s, %s, %s\n", rd, rd, rd);
    fprintf(out, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 52) & 0xFFFULL));
    fprintf(out, "\tshftli %s, 12\n", rd);
    fprintf(out, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 40) & 0xFFFULL));
    fprintf(out, "\tshftli %s, 12\n", rd);
    fprintf(out, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 28) & 0xFFFULL));
    fprintf(out, "\tshftli %s, 12\n", rd);
    fprintf(out, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 16) & 0xFFFULL));
    fprintf(out, "\tshftli %s, 12\n", rd);
    fprintf(out, "\taddi %s, %llu\n", rd, (unsigned long long)((L >> 4) & 0xFFFULL));
    fprintf(out, "\tshftli %s, 4\n", rd);
    fprintf(out, "\taddi %s, %llu\n", rd, (unsigned long long)(L & 0xFULL));
}

static const InstrDesc* lookup_instr_desc(const char *mnem) {
    for (int i = 0; instr_table[i].name; i++) {
        if (strcmp(mnem, instr_table[i].name) == 0) return &instr_table[i];
    }
    return NULL;
}

static int expected_operand_count_for_mnem(const char *mnem) {
    // macros + specials
    if (!strcmp(mnem, "clr")) return 1;
    if (!strcmp(mnem, "in")) return 2;
    if (!strcmp(mnem, "out")) return 2;
    if (!strcmp(mnem, "push")) return 1;
    if (!strcmp(mnem, "pop")) return 1;
    if (!strcmp(mnem, "halt")) return 0;
    if (!strcmp(mnem, "ld")) return 2;
    if (!strcmp(mnem, "mov")) return 2;
    if (!strcmp(mnem, "brr")) return 1;

    const InstrDesc *d = lookup_instr_desc(mnem);
    if (!d) return -1;

    switch (d->fmt) {
        case FMT_RRR:  return 3;
        case FMT_RI:   return 2;
        case FMT_RR:   return 2;
        case FMT_R:    return 1;
        case FMT_L:    return 1;
        case FMT_RRL:  return 3;
        case FMT_PRIV: return 4;
        case FMT_NONE: return 0;
        default: return -1;
    }
}

static int instr_size_bytes(const char *mnem) {
    if (!strcmp(mnem, "push")) return 8;
    if (!strcmp(mnem, "pop"))  return 8;
    if (!strcmp(mnem, "ld"))   return 48;
    return 4;
}

static void parseInput(FILE *input) {
    char raw[MAX_LINE];
    uint64_t pc = 0x1000;

    int section = -1; // 0 = code, 1 = data
    bool seen_code = false;
    bool seen_any_code_stmt = false;

    while (fgets(raw, sizeof(raw), input)) {
        enforce_leading_space_rule(raw);

        char clean[MAX_LINE];
        strcpy(clean, raw);
        trim_line_inplace(clean);

        if (!line_has_non_ws(clean)) continue;

        char *ptr = clean;
        while (isspace((unsigned char)*ptr)) ptr++;
        if (*ptr == '\0') continue;

        // Section directives must be alone (after trimming)
        if (strncmp(ptr, ".code", 5) == 0) {
            if (ptr[5] != '\0') dief("Unknown/extra tokens after .code", raw);
            section = 0;
            seen_code = true;
            continue;
        }
        if (strncmp(ptr, ".data", 5) == 0) {
            if (ptr[5] != '\0') dief("Unknown/extra tokens after .data", raw);
            if (!seen_code) dief(".data seen before .code", raw);
            section = 1;
            continue;
        }

        // Label line
        if (*ptr == ':') {
            // label must start at column 0
            if (raw[0] != ':') dief("Label must start at column 0", raw);
            enforce_label_only(ptr, raw);

            char labelbuf[256];
            if (sscanf(ptr + 1, "%255s", labelbuf) != 1) dief("Invalid label syntax", raw);
            add_label(labelbuf, pc, raw);
            continue;
        }

        // Statement line must begin with a tab
        enforce_tab_rule_if_statement(raw, ptr);

        if (section == -1) dief("Statement outside of .code/.data", raw);

        if (section == 1) {
            char *p2 = ptr;
            char *tok1 = parse_token(&p2);
            if (!tok1) dief("Malformed data line", raw);
            uint64_t v;
            if (!parse_u64_decimal_strict(tok1, &v)) {
                free(tok1);
                dief("Invalid data literal (must be unsigned 64-bit decimal)", raw);
            }
            free(tok1);
            char *tok2 = parse_token(&p2);
            if (tok2) {
                free(tok2);
                dief("Extra token in data line", raw);
            }
            pc += 8;
            continue;
        }

        // code statement: validate mnemonic exists + operand count at minimum
        char *p2 = ptr;
        char *mnem = parse_token(&p2);
        if (!mnem) dief("Malformed instruction line", raw);

        int expected = expected_operand_count_for_mnem(mnem);
        if (expected < 0) {
            free(mnem);
            dief("Unknown instruction mnemonic", raw);
        }

        int count = 0;
        char *t;
        while ((t = parse_token(&p2)) != NULL) {
            count++;
            free(t);
        }
        if (count != expected) {
            free(mnem);
            dief("Wrong number of operands", raw);
        }

        seen_any_code_stmt = true;
        pc += (uint64_t)instr_size_bytes(mnem);
        free(mnem);
    }

    if (!seen_code) dief("Missing .code section", NULL);
    if (!seen_any_code_stmt) dief(".code section has no statements", NULL);
}

static void generateIntermediate(FILE *input, FILE *intermediate) {
    char raw[MAX_LINE];
    int section = -1; // 0 = code, 1 = data
    int last_section_written = -2;

    uint64_t pc = 0x1000; // needed for brr label resolution

    while (fgets(raw, sizeof(raw), input)) {
        enforce_leading_space_rule(raw);

        char clean[MAX_LINE];
        strcpy(clean, raw);
        trim_line_inplace(clean);

        if (!line_has_non_ws(clean)) continue;

        char *ptr = clean;
        while (isspace((unsigned char)*ptr)) ptr++;
        if (*ptr == '\0') continue;

        if (strncmp(ptr, ".code", 5) == 0 && ptr[5] == '\0') {
            section = 0;
            if (last_section_written != 0) {
                fprintf(intermediate, ".code\n");
                last_section_written = 0;
            }
            continue;
        }
        if (strncmp(ptr, ".data", 5) == 0 && ptr[5] == '\0') {
            section = 1;
            if (last_section_written != 1) {
                fprintf(intermediate, ".data\n");
                last_section_written = 1;
            }
            continue;
        }

        if (*ptr == ':') {
            if (raw[0] != ':') dief("Label must start at column 0", raw);
            enforce_label_only(ptr, raw);
            continue;
        }

        enforce_tab_rule_if_statement(raw, ptr);
        if (section == -1) dief("Statement outside of .code/.data", raw);

        if (section == 1) {
            char *p2 = ptr;
            char *tok = parse_token(&p2);
            if (!tok) dief("Malformed data line", raw);

            uint64_t v;
            if (!parse_u64_decimal_strict(tok, &v)) {
                free(tok);
                dief("Invalid data literal (must be unsigned 64-bit decimal)", raw);
            }
            free(tok);

            char *tok2 = parse_token(&p2);
            if (tok2) {
                free(tok2);
                dief("Extra token in data line", raw);
            }

            fprintf(intermediate, "\t%llu\n", (unsigned long long)v);
            pc += 8;
            continue;
        }

        // code statement
        char *p2 = ptr;
        char *mnem = parse_token(&p2);
        if (!mnem) dief("Malformed instruction line", raw);

        // macros with strict register validation
        if (strcmp(mnem, "clr") == 0) {
            char *rd = parse_token(&p2);
            char *extra = parse_token(&p2);
            uint8_t rr;
            if (!rd || extra) { free(mnem); free(rd); free(extra); dief("Malformed clr", raw); }
            if (!parse_reg_num(rd, &rr)) { free(mnem); free(rd); dief("clr requires a valid register", raw); }
            m_clr(intermediate, rd);
            pc += 4;
            free(mnem); free(rd);
            continue;
        }
        if (strcmp(mnem, "in") == 0) {
            char *rd = parse_token(&p2);
            char *rs = parse_token(&p2);
            char *extra = parse_token(&p2);
            uint8_t rrd, rrs;
            if (!rd || !rs || extra) { free(mnem); free(rd); free(rs); free(extra); dief("Malformed in", raw); }
            if (!parse_reg_num(rd, &rrd) || !parse_reg_num(rs, &rrs)) { free(mnem); free(rd); free(rs); dief("in requires valid registers", raw); }
            m_in(intermediate, rd, rs);
            pc += 4;
            free(mnem); free(rd); free(rs);
            continue;
        }
        if (strcmp(mnem, "out") == 0) {
            char *rd = parse_token(&p2);
            char *rs = parse_token(&p2);
            char *extra = parse_token(&p2);
            uint8_t rrd, rrs;
            if (!rd || !rs || extra) { free(mnem); free(rd); free(rs); free(extra); dief("Malformed out", raw); }
            if (!parse_reg_num(rd, &rrd) || !parse_reg_num(rs, &rrs)) { free(mnem); free(rd); free(rs); dief("out requires valid registers", raw); }
            m_out(intermediate, rd, rs);
            pc += 4;
            free(mnem); free(rd); free(rs);
            continue;
        }
        if (strcmp(mnem, "push") == 0) {
            char *rd = parse_token(&p2);
            char *extra = parse_token(&p2);
            uint8_t rr;
            if (!rd || extra) { free(mnem); free(rd); free(extra); dief("Malformed push", raw); }
            if (!parse_reg_num(rd, &rr)) { free(mnem); free(rd); dief("push requires a valid register", raw); }
            m_push(intermediate, rd);
            pc += 8;
            free(mnem); free(rd);
            continue;
        }
        if (strcmp(mnem, "pop") == 0) {
            char *rd = parse_token(&p2);
            char *extra = parse_token(&p2);
            uint8_t rr;
            if (!rd || extra) { free(mnem); free(rd); free(extra); dief("Malformed pop", raw); }
            if (!parse_reg_num(rd, &rr)) { free(mnem); free(rd); dief("pop requires a valid register", raw); }
            m_pop(intermediate, rd);
            pc += 8;
            free(mnem); free(rd);
            continue;
        }
        if (strcmp(mnem, "halt") == 0) {
            char *extra = parse_token(&p2);
            if (extra) { free(mnem); free(extra); dief("halt takes no operands", raw); }
            m_halt(intermediate);
            pc += 4;
            free(mnem);
            continue;
        }
        if (strcmp(mnem, "ld") == 0) {
            char *rd = parse_token(&p2);
            char *L_str = parse_token(&p2);
            char *extra = parse_token(&p2);
            uint8_t rr;
            if (!rd || !L_str || extra) { free(mnem); free(rd); free(L_str); free(extra); dief("Malformed ld", raw); }
            if (!parse_reg_num(rd, &rr)) { free(mnem); free(rd); free(L_str); dief("ld requires a valid register", raw); }

            uint64_t L;
            if (L_str[0] == ':') {
                if (!is_valid_label_name(L_str + 1)) { free(mnem); free(rd); free(L_str); dief("Invalid label reference", raw); }
                L = get_addr(L_str + 1);
                if (L == (uint64_t)-1) { free(mnem); free(rd); free(L_str); dief("Unknown label in ld", raw); }
            } else {
                if (!parse_u64_anybase_strict(L_str, &L)) { free(mnem); free(rd); free(L_str); dief("Invalid literal in ld", raw); }
            }
            m_ld(intermediate, rd, L);
            pc += 48;
            free(mnem); free(rd); free(L_str);
            continue;
        }

        // Special: brr resolution if operand is label => PC-relative instruction count
        if (strcmp(mnem, "brr") == 0) {
            char *op1 = parse_token(&p2);
            char *extra = parse_token(&p2);
            if (!op1 || extra) { free(mnem); free(op1); free(extra); dief("Malformed brr", raw); }

            uint8_t r;
            if (parse_reg_num(op1, &r)) {
                fprintf(intermediate, "\tbrr %s\n", op1);
                pc += 4;
            } else {
                int64_t L_count = 0;
                if (op1[0] == ':') {
                    if (!is_valid_label_name(op1 + 1)) { free(mnem); free(op1); dief("Invalid label reference", raw); }
                    uint64_t target = get_addr(op1 + 1);
                    if (target == (uint64_t)-1) { free(mnem); free(op1); dief("Unknown label in brr", raw); }
                    // PC-relative: (target - (pc + 4)) / 4
                    L_count = (int64_t)((int64_t)target - (int64_t)(pc + 4)) / 4;
                } else {
                    // allow numeric instruction-count literal (signed decimal/hex)
                    char *end = NULL;
                    errno = 0;
                    long long tmp = strtoll(op1, &end, 0);
                    if (errno != 0 || !end || *end != '\0') { free(mnem); free(op1); dief("Invalid brr literal", raw); }
                    L_count = (int64_t)tmp;
                }
                if (L_count < -2048 || L_count > 2047) { free(mnem); free(op1); dief("brr offset out of signed 12-bit range", raw); }
                fprintf(intermediate, "\tbrr %lld\n", (long long)L_count);
                pc += 4;
            }

            free(mnem); free(op1);
            continue;
        }

        int expected = expected_operand_count_for_mnem(mnem);
        if (expected < 0) { free(mnem); dief("Unknown instruction mnemonic", raw); }

        fprintf(intermediate, "\t%s", mnem);

        char *tok = parse_token(&p2);
        int first = 1;
        while (tok) {
            if (tok[0] == ':') {
                if (!is_valid_label_name(tok + 1)) { free(tok); free(mnem); dief("Invalid label reference", raw); }
                uint64_t addr = get_addr(tok + 1);
                if (addr == (uint64_t)-1) { free(tok); free(mnem); dief("Unknown label referenced", raw); }

                free(tok);
                char buf[64];
                snprintf(buf, sizeof(buf), "%llu", (unsigned long long)addr);
                tok = my_strdup(buf);
                if (!tok) { free(mnem); dief("Out of memory", raw); }
            }

            fprintf(intermediate, "%s%s", (first ? " " : ", "), tok);
            first = 0;
            free(tok);
            tok = parse_token(&p2);
        }
        fprintf(intermediate, "\n");

        pc += 4;
        free(mnem);
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

static bool generateOutput(FILE *intermediate, FILE *output) {
    char raw[MAX_LINE];
    int section = -1; // 0 code, 1 data

    while (fgets(raw, sizeof(raw), intermediate)) {
        char clean[MAX_LINE];
        strcpy(clean, raw);
        trim_line_inplace(clean);

        if (!line_has_non_ws(clean)) continue;

        char *ptr = clean;
        while (isspace((unsigned char)*ptr)) ptr++;
        if (*ptr == '\0') continue;

        if (strncmp(ptr, ".code", 5) == 0 && ptr[5] == '\0') { section = 0; continue; }
        if (strncmp(ptr, ".data", 5) == 0 && ptr[5] == '\0') { section = 1; continue; }

        if (raw[0] != '\t') dief("Intermediate statement missing leading tab", raw);
        if (section == -1) dief("Intermediate content outside section", raw);

        // advance past tab
        if (*ptr == '\t') ptr++;

        if (section == 1) {
            // data: strict unsigned decimal
            char *p2 = ptr;
            char *tok = parse_token(&p2);
            if (!tok) dief("Bad data line in intermediate", raw);
            uint64_t v;
            if (!parse_u64_decimal_strict(tok, &v)) { free(tok); dief("Bad data literal in intermediate", raw); }
            free(tok);

            char *extra = parse_token(&p2);
            if (extra) { free(extra); dief("Extra token in data intermediate", raw); }

            write_u64(output, v);
            continue;
        }

        // code line
        char *p2 = ptr;
        char *op = parse_token(&p2);
        if (!op) continue;

        // mov is multi-form
        if (strcmp(op, "mov") == 0) {
            char *t1 = parse_token(&p2);
            char *t2 = parse_token(&p2);
            char *t3 = parse_token(&p2);
            if (!t1 || !t2 || t3) {
                free(op); free(t1); free(t2); free(t3);
                dief("Invalid mov in intermediate", raw);
            }

            uint8_t rd, rs;
            uint64_t imm;

            // mov rd, rs
            if (parse_reg_num(t1, &rd) && parse_reg_num(t2, &rs)) {
                write_instr(output, OP_MOV_RR, rd, rs, 0, 0);
            }
            // mov rd, L  (unsigned u12)
            else if (parse_reg_num(t1, &rd) && parse_u64_anybase_strict(t2, &imm)) {
                if (imm > MAX_IMMEDIATE_U12) {
                    free(op); free(t1); free(t2);
                    dief("Immediate too large for mov rd, L (u12)", raw);
                }
                write_instr(output, OP_MOV_RL, rd, 0, 0, (uint32_t)imm);
            }
            // mov rd, (rs)(L)
            else if (parse_reg_num(t1, &rd) && t2[0] == '(') {
                uint8_t base;
                int64_t off;
                if (!parse_mem_operand(t2, &base, &off)) {
                    free(op); free(t1); free(t2);
                    dief("Invalid mem operand for mov rd,(rs)(L)", raw);
                }
                uint32_t imm12 = imm12_signed_pack(off);
                if (imm12 == 0xFFFFFFFFu) {
                    free(op); free(t1); free(t2);
                    dief("mov offset out of signed 12-bit range", raw);
                }
                write_instr(output, OP_MOV_MR, rd, base, 0, imm12);
            }
            // mov (rd)(L), rs
            else if (t1[0] == '(' && parse_reg_num(t2, &rs)) {
                uint8_t base;
                int64_t off;
                if (!parse_mem_operand(t1, &base, &off)) {
                    free(op); free(t1); free(t2);
                    dief("Invalid mem operand for mov (rd)(L),rs", raw);
                }
                uint32_t imm12 = imm12_signed_pack(off);
                if (imm12 == 0xFFFFFFFFu) {
                    free(op); free(t1); free(t2);
                    dief("mov offset out of signed 12-bit range", raw);
                }
                write_instr(output, OP_MOV_RM, base, rs, 0, imm12);
            }
            else {
                free(op); free(t1); free(t2);
                dief("Invalid mov operands", raw);
            }

            free(op); free(t1); free(t2);
            continue;
        }

        // brr: register or signed u12 field (already resolved to literal in intermediate)
        if (strcmp(op, "brr") == 0) {
            char *t1 = parse_token(&p2);
            char *extra = parse_token(&p2);
            if (!t1 || extra) {
                free(op); free(t1); free(extra);
                dief("Invalid brr in intermediate", raw);
            }

            uint8_t rd;
            if (parse_reg_num(t1, &rd)) {
                write_instr(output, OP_BRR, rd, 0, 0, 0);
            } else {
                // signed literal
                char *end = NULL;
                errno = 0;
                long long v = strtoll(t1, &end, 0);
                if (errno != 0 || !end || *end != '\0') { free(op); free(t1); dief("Bad brr literal", raw); }
                uint32_t imm12 = imm12_signed_pack((int64_t)v);
                if (imm12 == 0xFFFFFFFFu) { free(op); free(t1); dief("brr literal out of signed 12-bit range", raw); }
                write_instr(output, OP_BRR_L, 0, 0, 0, imm12);
            }

            free(op); free(t1);
            continue;
        }

        // Lookup normal instruction
        const InstrDesc *desc = lookup_instr_desc(op);
        if (!desc) { free(op); dief("Unknown instruction in intermediate", raw); }

        char *t1 = parse_token(&p2);
        char *t2 = parse_token(&p2);
        char *t3 = parse_token(&p2);
        char *t4 = parse_token(&p2);
        char *t5 = parse_token(&p2);

        if (desc->fmt == FMT_RRR) {
            uint8_t rd, rs, rt;
            if (!t1 || !t2 || !t3 || t4) dief("Bad RRR format", raw);
            if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs) || !parse_reg_num(t3, &rt)) dief("Bad RRR operands", raw);
            write_instr(output, desc->opcode, rd, rs, rt, 0);
        }
        else if (desc->fmt == FMT_RI) {
            uint8_t rd;
            uint64_t imm;
            if (!t1 || !t2 || t3) dief("Bad RI format", raw);
            if (!parse_reg_num(t1, &rd)) dief("Bad RI reg", raw);
            if (!parse_u64_anybase_strict(t2, &imm)) dief("Bad RI literal", raw);
            if (imm > MAX_IMMEDIATE_U12) dief("RI literal out of u12 range", raw);
            write_instr(output, desc->opcode, rd, 0, 0, (uint32_t)imm);
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
            uint64_t imm;
            if (!t1 || t2) dief("Bad L format", raw);
            if (!parse_u64_anybase_strict(t1, &imm)) dief("Bad L literal", raw);
            if (imm > MAX_IMMEDIATE_U12) dief("L literal out of u12 range", raw);
            write_instr(output, desc->opcode, 0, 0, 0, (uint32_t)imm);
        }
        else if (desc->fmt == FMT_RRL) {
            uint8_t rd, rs;
            uint64_t imm;
            if (!t1 || !t2 || !t3 || t4) dief("Bad RRL format", raw);
            if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs)) dief("Bad RRL regs", raw);
            if (!parse_u64_anybase_strict(t3, &imm)) dief("Bad RRL literal", raw);
            if (imm > MAX_IMMEDIATE_U12) dief("RRL literal out of u12 range", raw);
            write_instr(output, desc->opcode, rd, rs, 0, (uint32_t)imm);
        }
        else if (desc->fmt == FMT_PRIV) {
            uint8_t rd, rs, rt;
            uint64_t imm;
            if (!t1 || !t2 || !t3 || !t4 || t5) dief("Bad PRIV format", raw);
            if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs) || !parse_reg_num(t3, &rt)) dief("Bad PRIV regs", raw);
            if (!parse_u64_anybase_strict(t4, &imm)) dief("Bad PRIV literal", raw);
            if (imm > MAX_IMMEDIATE_U12) dief("PRIV literal out of u12 range", raw);
            write_instr(output, desc->opcode, rd, rs, rt, (uint32_t)imm);
        }
        else if (desc->fmt == FMT_NONE) {
            if (t1) dief("Unexpected operand for no-operand instruction", raw);
            write_instr(output, desc->opcode, 0, 0, 0, 0);
        }
        else {
            dief("Unhandled instruction format", raw);
        }

        free(op);
        free(t1); free(t2); free(t3); free(t4); free(t5);
    }

    return true;
}

static void clearFile(const char* path) {
    FILE *f = fopen(path, "w");
    if (f) fclose(f);
}

int main(int argc, char *argv[]) {
    if (argc != 4) {
        fprintf(stderr, "Usage: %s <input.tk> <intermediate.tk> <output.tko>\n", argv[0]);
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

    parseInput(input);
    rewind(input);
    generateIntermediate(input, intermediate);

    fclose(input);
    fclose(intermediate);

    FILE *intermediate2 = fopen(argv[2], "r");
    if (!intermediate2) {
        fprintf(stderr, "Could not reopen intermediate\n");
        fclose(output);
        return 1;
    }

    bool ok = generateOutput(intermediate2, output);
    fclose(intermediate2);
    fclose(output);

    if (!ok) {
        clearFile(argv[2]);
        return 1;
    }

    return 0;
}
