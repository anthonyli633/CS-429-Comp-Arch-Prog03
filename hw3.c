#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>

#define MAX_LABELS 1024
#define MAX_IMM12_U 0xFFFULL

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
    OP_BRR_L  = 0x0A,   // brr L (imm12 signed)
    OP_BRNZ   = 0x0B,
    OP_CALL   = 0x0C,
    OP_RETURN = 0x0D,
    OP_BRGT   = 0x0E,
    OP_PRIV   = 0x0F,
    OP_MOV_MR = 0x10,   // mov rd, (rs)(off)
    OP_MOV_RR = 0x11,   // mov rd, rs
    OP_MOV_RL = 0x12,   // mov rd, imm12
    OP_MOV_RM = 0x13,   // mov (rd)(off), rs
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
    FMT_RI,     // rd, imm12 (unsigned)
    FMT_RR,     // rd, rs
    FMT_R,      // rd
    FMT_L,      // imm12 (unsigned)
    FMT_RRL,    // rd, rs, imm12 (unsigned)
    FMT_PRIV,   // rd, rs, rt, imm12 (unsigned)
    FMT_NONE
} InstrFormat;

typedef struct {
    const char *name;
    InstrFormat fmt;
    Opcode opcode;
} InstrDesc;

static const InstrDesc instr_table[] = {
    { "add",    FMT_RRR,  OP_ADD   },
    { "addi",   FMT_RI,   OP_ADDI  },
    { "sub",    FMT_RRR,  OP_SUB   },
    { "subi",   FMT_RI,   OP_SUBI  },
    { "mul",    FMT_RRR,  OP_MUL   },
    { "div",    FMT_RRR,  OP_DIV   },
    { "and",    FMT_RRR,  OP_AND   },
    { "or",     FMT_RRR,  OP_OR    },
    { "xor",    FMT_RRR,  OP_XOR   },
    { "not",    FMT_RR,   OP_NOT   },   // not rd, rs
    { "shftr",  FMT_RRR,  OP_SHFTR },
    { "shftri", FMT_RI,   OP_SHFTRI},
    { "shftl",  FMT_RRR,  OP_SHFTL },
    { "shftli", FMT_RI,   OP_SHFTLI},
    { "br",     FMT_R,    OP_BR    },
    { "brnz",   FMT_RR,   OP_BRNZ  },
    { "call",   FMT_R,    OP_CALL  },
    { "return", FMT_NONE, OP_RETURN},
    { "brgt",   FMT_RRR,  OP_BRGT  },
    { "priv",   FMT_PRIV, OP_PRIV  },
    { "addf",   FMT_RRR,  OP_ADDF  },
    { "subf",   FMT_RRR,  OP_SUBF  },
    { "mulf",   FMT_RRR,  OP_MULF  },
    { "divf",   FMT_RRR,  OP_DIVF  },
    { NULL,     0,        0        },
};


typedef struct {
    char name[256];
    uint64_t addr; // byte address
} Label;

static Label labels[MAX_LABELS];
static int label_count = 0;

static uint64_t get_addr(const char *label) {
    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, label) == 0) return labels[i].addr;
    }
    return (uint64_t)-1;
}

static void add_label(const char *name, uint64_t addr) {
    if (label_count >= MAX_LABELS) {
        fprintf(stderr, "Too many labels\n");
        exit(1);
    }
    strncpy(labels[label_count].name, name, sizeof(labels[label_count].name) - 1);
    labels[label_count].name[sizeof(labels[label_count].name) - 1] = '\0';
    labels[label_count].addr = addr;
    label_count++;
}


static void rstrip(char *s) {
    size_t n = strlen(s);
    while (n > 0 && isspace((unsigned char)s[n - 1])) s[--n] = '\0';
}

static char *my_strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *p = (char*)malloc(len);
    if (p) memcpy(p, s, len);
    return p;
}

static char* parse_token(char **p) {
    while (**p && (isspace((unsigned char)**p) || **p == ',')) (*p)++;
    if (**p == '\0') return NULL;

    char token[1024];
    int i = 0;
    while (**p && !isspace((unsigned char)**p) && **p != ',') {
        if (i < (int)sizeof(token) - 1) token[i++] = **p;
        (*p)++;
    }
    token[i] = '\0';
    return my_strdup(token);
}


static bool parse_u64_literal(const char *s, uint64_t *out) {
    if (!s || !*s) return false;
    if (s[0] == ':') return false;
    if (s[0] == '-') return false;

    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 0);
    if (errno != 0 || end == s || *end != '\0') return false;
    if (out) *out = (uint64_t)v;
    return true;
}

static bool parse_i64_literal(const char *s, int64_t *out) {
    if (!s || !*s) return false;
    if (s[0] == ':') return false;

    errno = 0;
    char *end = NULL;
    long long v = strtoll(s, &end, 0);
    if (errno != 0 || end == s || *end != '\0') return false;
    if (out) *out = (int64_t)v;
    return true;
}

static const char* valid_registers[] = {
    "r0","r1","r2","r3","r4","r5","r6","r7",
    "r8","r9","r10","r11","r12","r13","r14","r15",
    "r16","r17","r18","r19","r20","r21","r22","r23",
    "r24","r25","r26","r27","r28","r29","r30","r31"
};

static bool parse_reg_num(const char *tok, uint8_t *out) {
    if (!tok) return false;
    for (int i = 0; i < 32; i++) {
        if (strcmp(tok, valid_registers[i]) == 0) {
            if (out) *out = (uint8_t)i;
            return true;
        }
    }
    return false;
}

// mem operand: (rX)(off)
bool parse_mem_operand(const char *tok, uint8_t *base, int64_t *off) {
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

// signed imm12: returns 0xFFFFFFFF on out-of-range
uint32_t imm12_signed(int64_t x) {
    if (x < -2048 || x > 2047) return 0xFFFFFFFFu;
    return (uint32_t)(x & 0xFFF);
}


static const InstrDesc* find_desc(const char *op) {
    for (int i = 0; instr_table[i].name; i++) {
        if (strcmp(op, instr_table[i].name) == 0) return &instr_table[i];
    }
    return NULL;
}

static void require_no_extra(char **p, const char *line) {
    char *x = parse_token(p);
    if (x) {
        fprintf(stderr, "Extra token '%s' in line: %s\n", x, line);
        exit(1);
    }
}

static void require_reg_tok(char *tok, const char *line) {
    if (!tok || !parse_reg_num(tok, NULL)) {
        fprintf(stderr, "Bad register in line: %s\n", line);
        exit(1);
    }
}

static void require_u12_tok(char *tok, const char *line) {
    uint64_t v;
    if (!tok || !parse_u64_literal(tok, &v) || v > MAX_IMM12_U) {
        fprintf(stderr, "Bad 12-bit literal in line: %s\n", line);
        exit(1);
    }
}


static void macro_clr(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\txor %s, %s, %s\n", rd, rd, rd);
}
static void macro_in(FILE *intermediate, const char *rd, const char *rs) {
    fprintf(intermediate, "\tpriv %s, %s, r0, 3\n", rd, rs);
}
static void macro_out(FILE *intermediate, const char *rd, const char *rs) {
    fprintf(intermediate, "\tpriv %s, %s, r0, 4\n", rd, rs);
}
static void macro_push(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\tmov (r31)(-8), %s\n", rd);
    fprintf(intermediate, "\tsubi r31, 8\n");
}
static void macro_pop(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\tmov %s, (r31)(0)\n", rd);
    fprintf(intermediate, "\taddi r31, 8\n");
}
static void macro_halt(FILE *intermediate) {
    fprintf(intermediate, "\tpriv r0, r0, r0, 0\n");
}
static void macro_ld(FILE *intermediate, const char *rd, uint64_t L) {
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

static void parseInput(FILE *input) {
    char line[1024];
    int section = -1; // 0 code, 1 data
    uint64_t pc = 0x1000;

    while (fgets(line, sizeof(line), input)) {
        rstrip(line);

        char *p = line;
        if (*p == ';' || *p == '\0') continue;

        if (*p == ':') {
            p++;
            char *label = parse_token(&p);
            if (!label) { fprintf(stderr, "Empty label\n"); exit(1); }

            // [A-Za-z_][A-Za-z0-9_]*
            if (!(isalpha((unsigned char)label[0]) || label[0] == '_')) {
                fprintf(stderr, "Invalid label name: %s\n", label);
                exit(1);
            }
            for (char *q = label; *q; q++) {
                if (!(isalnum((unsigned char)*q) || *q == '_')) {
                    fprintf(stderr, "Invalid label name: %s\n", label);
                    exit(1);
                }
            }
            if (get_addr(label) != (uint64_t)-1) {
                fprintf(stderr, "Duplicate label: %s\n", label);
                exit(1);
            }

            add_label(label, pc);
            free(label);
            require_no_extra(&p, line);
            continue;
        }

        if (*p == '.') {
            if (strcmp(p, ".code") == 0) { section = 0; continue; }
            if (strcmp(p, ".data") == 0) { section = 1; continue; }
            fprintf(stderr, "Unknown section directive: %s\n", p);
            exit(1);
        }

        if (*p != '\t') {
            fprintf(stderr, "Syntax error (expected tab): %s\n", line);
            exit(1);
        }
        p++; // skip tab

        if (section == -1) {
            fprintf(stderr, "Content outside .code/.data: %s\n", line);
            exit(1);
        }

        if (section == 1) {
            char *tok = parse_token(&p);
            uint64_t v;
            if (!tok || !parse_u64_literal(tok, &v)) {
                fprintf(stderr, "Invalid data literal: %s\n", line);
                exit(1);
            }
            free(tok);
            require_no_extra(&p, line);
            pc += 8;
            continue;
        }

        // section == code: validate format and update pc for macro expansion
        char *op = parse_token(&p);
        if (!op) { fprintf(stderr, "Missing opcode: %s\n", line); exit(1); }

        int instr_count = 1; // default 1 emitted instruction

        if (strcmp(op, "clr") == 0) {
            char *rd = parse_token(&p);
            require_reg_tok(rd, line);
            free(rd);
            require_no_extra(&p, line);
        } else if (strcmp(op, "halt") == 0) {
            require_no_extra(&p, line);
        } else if (strcmp(op, "push") == 0 || strcmp(op, "pop") == 0) {
            char *rd = parse_token(&p);
            require_reg_tok(rd, line);
            free(rd);
            require_no_extra(&p, line);
            instr_count = 2;
        } else if (strcmp(op, "in") == 0 || strcmp(op, "out") == 0) {
            char *rd = parse_token(&p);
            char *rs = parse_token(&p);
            require_reg_tok(rd, line);
            require_reg_tok(rs, line);
            free(rd); free(rs);
            require_no_extra(&p, line);
        } else if (strcmp(op, "ld") == 0) {
            char *rd = parse_token(&p);
            char *L  = parse_token(&p);
            require_reg_tok(rd, line);
            if (!L) { fprintf(stderr, "Malformed ld: %s\n", line); exit(1); }
            if (!(L[0] == ':' || parse_u64_literal(L, NULL))) {
                fprintf(stderr, "Bad ld operand: %s\n", line);
                exit(1);
            }
            free(rd); free(L);
            require_no_extra(&p, line);
            instr_count = 12;
        } else if (strcmp(op, "brr") == 0) {
            // one operand, can be reg, signed literal, or :label
            char *t1 = parse_token(&p);
            if (!t1) { fprintf(stderr, "Malformed brr: %s\n", line); exit(1); }
            require_no_extra(&p, line);

            if (parse_reg_num(t1, NULL)) {
                // ok
            } else if (t1[0] == ':') {
                // ok (must exist)
                if (get_addr(t1 + 1) == (uint64_t)-1) {
                    fprintf(stderr, "Unknown label in brr: %s\n", line);
                    exit(1);
                }
            } else {
                int64_t v;
                if (!parse_i64_literal(t1, &v) || imm12_signed(v) == 0xFFFFFFFFu) {
                    fprintf(stderr, "Bad brr immediate: %s\n", line);
                    exit(1);
                }
            }
            free(t1);
        } else if (strcmp(op, "mov") == 0) {
            // allow: mov rd, rs | mov rd, imm | mov rd, (rs)(off) | mov (rd)(off), rs
            char *t1 = parse_token(&p);
            char *t2 = parse_token(&p);
            if (!t1 || !t2) { fprintf(stderr, "Malformed mov: %s\n", line); exit(1); }
            require_no_extra(&p, line);

            bool ok = false;
            uint8_t r;
            uint64_t u;
            int64_t s;
            uint8_t base;
            if (parse_reg_num(t1, NULL) && parse_reg_num(t2, NULL)) ok = true;
            else if (parse_reg_num(t1, NULL) && parse_u64_literal(t2, &u) && u <= MAX_IMM12_U) ok = true;
            else if (parse_reg_num(t1, NULL) && parse_mem_operand(t2, &base, &s) && imm12_signed(s) != 0xFFFFFFFFu) ok = true;
            else if (parse_mem_operand(t1, &base, &s) && imm12_signed(s) != 0xFFFFFFFFu && parse_reg_num(t2, &r)) ok = true;

            if (!ok) { fprintf(stderr, "Invalid mov operands: %s\n", line); exit(1); }
            free(t1); free(t2);
        } else {
            const InstrDesc *d = find_desc(op);
            if (!d) { fprintf(stderr, "Unknown instruction: %s\n", line); exit(1); }

            char *t1 = parse_token(&p);
            char *t2 = parse_token(&p);
            char *t3 = parse_token(&p);
            char *t4 = parse_token(&p);
            char *t5 = parse_token(&p);

            switch (d->fmt) {
                case FMT_RRR:
                    require_reg_tok(t1, line); require_reg_tok(t2, line); require_reg_tok(t3, line);
                    if (t4 || t5) { fprintf(stderr, "Too many operands: %s\n", line); exit(1); }
                    break;
                case FMT_RR:
                    require_reg_tok(t1, line); require_reg_tok(t2, line);
                    if (t3 || t4 || t5) { fprintf(stderr, "Too many operands: %s\n", line); exit(1); }
                    break;
                case FMT_RI:
                    require_reg_tok(t1, line); require_u12_tok(t2, line);
                    if (t3 || t4 || t5) { fprintf(stderr, "Too many operands: %s\n", line); exit(1); }
                    break;
                case FMT_R:
                    require_reg_tok(t1, line);
                    if (t2 || t3 || t4 || t5) { fprintf(stderr, "Too many operands: %s\n", line); exit(1); }
                    break;
                case FMT_PRIV:
                    require_reg_tok(t1, line); require_reg_tok(t2, line); require_reg_tok(t3, line); require_u12_tok(t4, line);
                    if (t5) { fprintf(stderr, "Too many operands: %s\n", line); exit(1); }
                    break;
                case FMT_NONE:
                    if (t1 || t2 || t3 || t4 || t5) { fprintf(stderr, "Unexpected operand: %s\n", line); exit(1); }
                    break;
                default:
                    fprintf(stderr, "Unhandled format in stage1: %s\n", line);
                    exit(1);
            }

            free(t1); free(t2); free(t3); free(t4); free(t5);
        }

        free(op);
        pc += 4ULL * (uint64_t)instr_count;
    }
}

static void generateIntermediate(FILE *input, FILE *intermediate) {
    char line[1024];
    int section = -1;

    while (fgets(line, sizeof(line), input)) {
        rstrip(line);

        char *p = line;
        if (*p == ';' || *p == '\0') continue;

        if (*p == ':') continue; // labels removed in intermediate
        if (*p == '.') {
            if (strcmp(p, ".code") == 0) { if (section != 0) fprintf(intermediate, ".code\n"); section = 0; }
            else if (strcmp(p, ".data") == 0) { if (section != 1) fprintf(intermediate, ".data\n"); section = 1; }
            else { fprintf(stderr, "Unknown section directive: %s\n", p); exit(1); }
            continue;
        }

        if (*p != '\t') { fprintf(stderr, "Syntax error (expected tab): %s\n", line); exit(1); }
        p++;

        if (section == 0) {
            char *op = parse_token(&p);
            if (!op) continue;

            if (strcmp(op, "clr") == 0) {
                char *rd = parse_token(&p);
                require_reg_tok(rd, line);
                require_no_extra(&p, line);
                macro_clr(intermediate, rd);
                free(rd);
            } else if (strcmp(op, "in") == 0) {
                char *rd = parse_token(&p);
                char *rs = parse_token(&p);
                require_reg_tok(rd, line);
                require_reg_tok(rs, line);
                require_no_extra(&p, line);
                macro_in(intermediate, rd, rs);
                free(rd); free(rs);
            } else if (strcmp(op, "out") == 0) {
                char *rd = parse_token(&p);
                char *rs = parse_token(&p);
                require_reg_tok(rd, line);
                require_reg_tok(rs, line);
                require_no_extra(&p, line);
                macro_out(intermediate, rd, rs);
                free(rd); free(rs);
            } else if (strcmp(op, "push") == 0) {
                char *rd = parse_token(&p);
                require_reg_tok(rd, line);
                require_no_extra(&p, line);
                macro_push(intermediate, rd);
                free(rd);
            } else if (strcmp(op, "pop") == 0) {
                char *rd = parse_token(&p);
                require_reg_tok(rd, line);
                require_no_extra(&p, line);
                macro_pop(intermediate, rd);
                free(rd);
            } else if (strcmp(op, "halt") == 0) {
                require_no_extra(&p, line);
                macro_halt(intermediate);
            } else if (strcmp(op, "ld") == 0) {
                char *rd = parse_token(&p);
                char *L_str = parse_token(&p);
                require_reg_tok(rd, line);
                if (!L_str) { fprintf(stderr, "Malformed ld: %s\n", line); exit(1); }
                require_no_extra(&p, line);

                uint64_t L;
                if (L_str[0] == ':') {
                    L = get_addr(L_str + 1);
                    if (L == (uint64_t)-1) {
                        fprintf(stderr, "Unknown label in ld: %s\n", L_str);
                        exit(1);
                    }
                } else {
                    if (!parse_u64_literal(L_str, &L)) {
                        fprintf(stderr, "Invalid literal in ld: %s\n", L_str);
                        exit(1);
                    }
                }

                macro_ld(intermediate, rd, L);
                free(rd);
                free(L_str);
            } else {
                // passthrough, but allow tokens (including :label)
                fprintf(intermediate, "\t%s", op);
                int first = 1;
                char *tok = parse_token(&p);
                while (tok) {
                    fprintf(intermediate, "%s%s", first ? " " : ", ", tok);
                    first = 0;
                    free(tok);
                    tok = parse_token(&p);
                }
                fprintf(intermediate, "\n");
            }

            free(op);
        } else if (section == 1) {
            char *tok = parse_token(&p);
            if (!tok) { fprintf(stderr, "Malformed data line: %s\n", line); exit(1); }
            require_no_extra(&p, line);
            fprintf(intermediate, "\t%s\n", tok);
            free(tok);
        } else {
            fprintf(stderr, "Content outside section: %s\n", line);
            exit(1);
        }
    }
}

// -------------------------- Binary writer --------------------------

static void write_u32(FILE *out, uint32_t w) { fwrite(&w, sizeof(w), 1, out); }
static void write_u64(FILE *out, uint64_t x) { fwrite(&x, sizeof(x), 1, out); }

static void write_instr(FILE *out, Opcode opcode,
                        uint8_t rd, uint8_t rs, uint8_t rt,
                        uint32_t imm12) {
    if (opcode > 0x1F) {
        fprintf(stderr, "Opcode out of 5-bit range: 0x%X\n", opcode);
        exit(1);
    }
    if (rd > 31 || rs > 31 || rt > 31) {
        fprintf(stderr, "Register out of range rd=%u rs=%u rt=%u\n", rd, rs, rt);
        exit(1);
    }
    if (imm12 > 0xFFF) {
        fprintf(stderr, "Immediate out of 12-bit range: %u\n", imm12);
        exit(1);
    }

    uint32_t inst = 0;
    inst |= ((uint32_t)opcode & 0x1F) << 27;
    inst |= ((uint32_t)rd     & 0x1F) << 22;
    inst |= ((uint32_t)rs     & 0x1F) << 17;
    inst |= ((uint32_t)rt     & 0x1F) << 12;
    inst |= ((uint32_t)imm12  & 0xFFF);
    write_u32(out, inst);
}

static void clearFile(const char* path) {
    FILE *f = fopen(path, "w");
    if (f) fclose(f);
}

// -------------------------- Stage 2: assemble .int to .tko --------------------------

static bool generateOutput(FILE *intermediate, FILE *output) {
    char line[1024];
    int section = -1; // 0 code, 1 data

    uint64_t pc = 0x1000; // byte PC in code section (for brr label offsets)

    while (fgets(line, sizeof(line), intermediate)) {
        rstrip(line);

        char *p = line;
        while (isspace((unsigned char)*p)) p++;
        if (*p == '\0') continue;

        if (strcmp(p, ".code") == 0) { section = 0; pc = 0x1000; continue; }
        if (strcmp(p, ".data") == 0) { section = 1; continue; }

        if (*p != '\t') continue;
        p++;

        if (section == 0) {
            char *op = parse_token(&p);
            if (!op) continue;

            // mov (special)
            if (strcmp(op, "mov") == 0) {
                char *t1 = parse_token(&p);
                char *t2 = parse_token(&p);
                char *extra = parse_token(&p);
                if (!t1 || !t2 || extra) {
                    fprintf(stderr, "Invalid mov: %s\n", line);
                    free(t1); free(t2); free(extra); free(op);
                    return false;
                }

                uint8_t rd, rs;
                uint64_t immu;

                if (parse_reg_num(t1, &rd) && parse_reg_num(t2, &rs)) {
                    write_instr(output, OP_MOV_RR, rd, rs, 0, 0);
                    pc += 4;
                } else if (parse_reg_num(t1, &rd) && parse_u64_literal(t2, &immu) && immu <= MAX_IMM12_U) {
                    write_instr(output, OP_MOV_RL, rd, 0, 0, (uint32_t)immu);
                    pc += 4;
                } else if (parse_reg_num(t1, &rd) && t2[0] == '(') {
                    uint8_t base;
                    int64_t off;
                    if (!parse_mem_operand(t2, &base, &off)) {
                        fprintf(stderr, "Bad mov mem operand: %s\n", line);
                        free(t1); free(t2); free(op);
                        return false;
                    }
                    uint32_t imm12 = imm12_signed(off);
                    if (imm12 == 0xFFFFFFFFu) {
                        fprintf(stderr, "mov offset out of range: %s\n", line);
                        free(t1); free(t2); free(op);
                        return false;
                    }
                    write_instr(output, OP_MOV_MR, rd, base, 0, imm12);
                    pc += 4;
                } else if (t1[0] == '(' && parse_reg_num(t2, &rs)) {
                    uint8_t base;
                    int64_t off;
                    if (!parse_mem_operand(t1, &base, &off)) {
                        fprintf(stderr, "Bad mov mem operand: %s\n", line);
                        free(t1); free(t2); free(op);
                        return false;
                    }
                    uint32_t imm12 = imm12_signed(off);
                    if (imm12 == 0xFFFFFFFFu) {
                        fprintf(stderr, "mov offset out of range: %s\n", line);
                        free(t1); free(t2); free(op);
                        return false;
                    }
                    write_instr(output, OP_MOV_RM, base, rs, 0, imm12);
                    pc += 4;
                } else {
                    fprintf(stderr, "Invalid mov operands: %s\n", line);
                    free(t1); free(t2); free(op);
                    return false;
                }

                free(t1); free(t2); free(op);
                continue;
            }

            // brr (special)
            if (strcmp(op, "brr") == 0) {
                char *t1 = parse_token(&p);
                char *extra = parse_token(&p);
                if (!t1 || extra) {
                    fprintf(stderr, "Invalid brr: %s\n", line);
                    free(t1); free(extra); free(op);
                    return false;
                }

                uint8_t rd;
                if (parse_reg_num(t1, &rd)) {
                    write_instr(output, OP_BRR, rd, 0, 0, 0);
                    pc += 4;
                } else if (t1[0] == ':') {
                    uint64_t target = get_addr(t1 + 1);
                    if (target == (uint64_t)-1) {
                        fprintf(stderr, "Unknown label in brr: %s\n", line);
                        free(t1); free(op);
                        return false;
                    }
                    // PC-relative offset in WORDS to next instruction
                    // off_words = (target - (pc + 4)) / 4
                    int64_t off_words = (int64_t)((int64_t)target - (int64_t)(pc + 4)) / 4;
                    uint32_t imm12 = imm12_signed(off_words);
                    if (imm12 == 0xFFFFFFFFu) {
                        fprintf(stderr, "brr label offset out of range: %s\n", line);
                        free(t1); free(op);
                        return false;
                    }
                    write_instr(output, OP_BRR_L, 0, 0, 0, imm12);
                    pc += 4;
                } else {
                    // immediate is signed 12-bit (already word offset)
                    int64_t v;
                    if (!parse_i64_literal(t1, &v)) {
                        fprintf(stderr, "Bad brr immediate: %s\n", line);
                        free(t1); free(op);
                        return false;
                    }
                    uint32_t imm12 = imm12_signed(v);
                    if (imm12 == 0xFFFFFFFFu) {
                        fprintf(stderr, "brr immediate out of range: %s\n", line);
                        free(t1); free(op);
                        return false;
                    }
                    write_instr(output, OP_BRR_L, 0, 0, 0, imm12);
                    pc += 4;
                }

                free(t1); free(op);
                continue;
            }

            // other ops via table
            const InstrDesc *desc = find_desc(op);
            if (!desc) {
                fprintf(stderr, "Unknown instruction in intermediate: %s\n", op);
                free(op);
                return false;
            }

            char *t1 = parse_token(&p);
            char *t2 = parse_token(&p);
            char *t3 = parse_token(&p);
            char *t4 = parse_token(&p);
            char *t5 = parse_token(&p);

            if (desc->fmt == FMT_RRR) {
                uint8_t rd, rs, rt;
                if (!t1 || !t2 || !t3 || t4 || t5) {
                    fprintf(stderr, "Bad RRR format: %s\n", line);
                    free(op); free(t1); free(t2); free(t3); free(t4); free(t5);
                    return false;
                }
                if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs) || !parse_reg_num(t3, &rt)) {
                    fprintf(stderr, "Bad RRR operands: %s\n", line);
                    free(op); free(t1); free(t2); free(t3);
                    return false;
                }
                write_instr(output, desc->opcode, rd, rs, rt, 0);
                pc += 4;
            } else if (desc->fmt == FMT_RI) {
                uint8_t rd;
                uint64_t imm;
                if (!t1 || !t2 || t3 || t4 || t5) {
                    fprintf(stderr, "Bad RI format: %s\n", line);
                    free(op); free(t1); free(t2); free(t3); free(t4); free(t5);
                    return false;
                }
                if (!parse_reg_num(t1, &rd) || !parse_u64_literal(t2, &imm) || imm > MAX_IMM12_U) {
                    fprintf(stderr, "Bad RI operands: %s\n", line);
                    free(op); free(t1); free(t2);
                    return false;
                }
                write_instr(output, desc->opcode, rd, 0, 0, (uint32_t)imm);
                pc += 4;
            } else if (desc->fmt == FMT_RR) {
                uint8_t rd, rs;
                if (!t1 || !t2 || t3 || t4 || t5) {
                    fprintf(stderr, "Bad RR format: %s\n", line);
                    free(op); free(t1); free(t2); free(t3); free(t4); free(t5);
                    return false;
                }
                if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs)) {
                    fprintf(stderr, "Bad RR operands: %s\n", line);
                    free(op); free(t1); free(t2);
                    return false;
                }
                write_instr(output, desc->opcode, rd, rs, 0, 0);
                pc += 4;
            } else if (desc->fmt == FMT_R) {
                uint8_t rd;
                if (!t1 || t2 || t3 || t4 || t5) {
                    fprintf(stderr, "Bad R format: %s\n", line);
                    free(op); free(t1); free(t2); free(t3); free(t4); free(t5);
                    return false;
                }
                if (!parse_reg_num(t1, &rd)) {
                    fprintf(stderr, "Bad R operand: %s\n", line);
                    free(op); free(t1);
                    return false;
                }
                write_instr(output, desc->opcode, rd, 0, 0, 0);
                pc += 4;
            } else if (desc->fmt == FMT_PRIV) {
                uint8_t rd, rs, rt;
                uint64_t imm;
                if (!t1 || !t2 || !t3 || !t4 || t5) {
                    fprintf(stderr, "Bad PRIV format: %s\n", line);
                    free(op); free(t1); free(t2); free(t3); free(t4); free(t5);
                    return false;
                }
                if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs) || !parse_reg_num(t3, &rt) ||
                    !parse_u64_literal(t4, &imm) || imm > MAX_IMM12_U) {
                    fprintf(stderr, "Bad PRIV operands: %s\n", line);
                    free(op); free(t1); free(t2); free(t3); free(t4);
                    return false;
                }
                write_instr(output, desc->opcode, rd, rs, rt, (uint32_t)imm);
                pc += 4;
            } else if (desc->fmt == FMT_NONE) {
                if (t1 || t2 || t3 || t4 || t5) {
                    fprintf(stderr, "Unexpected operands: %s\n", line);
                    free(op); free(t1); free(t2); free(t3); free(t4); free(t5);
                    return false;
                }
                write_instr(output, desc->opcode, 0, 0, 0, 0);
                pc += 4;
            } else {
                fprintf(stderr, "Unhandled format in stage2: %s\n", op);
                free(op);
                return false;
            }

            free(op);
            free(t1); free(t2); free(t3); free(t4); free(t5);
        } else if (section == 1) {
            char *tok = parse_token(&p);
            uint64_t v;
            if (!tok || !parse_u64_literal(tok, &v)) {
                fprintf(stderr, "Bad data literal: %s\n", line);
                free(tok);
                return false;
            }
            char *extra = parse_token(&p);
            if (extra) {
                fprintf(stderr, "Extra token in data: %s\n", line);
                free(tok); free(extra);
                return false;
            }
            write_u64(output, v);
            free(tok);
        } else {
            fprintf(stderr, "Content outside section: %s\n", line);
            return false;
        }
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
        fprintf(stderr, "Could not open input/intermediate/output\n");
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
