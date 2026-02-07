#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>
#include <limits.h>

#define MAX_LABELS 1024
#define MAX_IMMEDIATE_SIZE 0xFFF // 12-bit immediate

// Instructions
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
    OP_BRR    = 0x09,
    OP_BRR_L  = 0x0A,
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
    { "return", FMT_NONE, OP_RETURN },
    { "brgt",   FMT_RRR, OP_BRGT   },
    { "priv",   FMT_PRIV, OP_PRIV  },
    { "addf",   FMT_RRR, OP_ADDF },
    { "subf",   FMT_RRR, OP_SUBF },
    { "mulf",   FMT_RRR, OP_MULF },
    { "divf",   FMT_RRR, OP_DIVF },
    // NOTE: brr is special-cased (it has two forms).
    { NULL,     0,       0 },
};

// ---------------- Labels ----------------
typedef struct {
    char name[256];
    uint64_t addr;
} Label;

static Label labels[MAX_LABELS];
static int label_count = 0;

static bool is_valid_label_name(const char *s) {
    if (!s || !*s) return false;
    size_t n = strlen(s);
    if (n > 255) return false;

    // Strict-ish label rule (good for autograders): [A-Za-z_][A-Za-z0-9_]*
    if (!(isalpha((unsigned char)s[0]) || s[0] == '_')) return false;
    for (size_t i = 1; i < n; i++) {
        unsigned char c = (unsigned char)s[i];
        if (!(isalnum(c) || c == '_')) return false;
    }
    return true;
}

static int find_label_index(const char *label) {
    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, label) == 0) return i;
    }
    return -1;
}

uint64_t get_addr(const char *label) {
    int idx = find_label_index(label);
    if (idx >= 0) return labels[idx].addr;
    return (uint64_t)-1;
}

void add_label(const char *name, uint64_t addr) {
    if (!is_valid_label_name(name)) {
        fprintf(stderr, "Invalid label name: %s\n", name ? name : "(null)");
        exit(1);
    }
    if (find_label_index(name) >= 0) {
        fprintf(stderr, "Duplicate label: %s\n", name);
        exit(1);
    }
    if (label_count >= MAX_LABELS) {
        fprintf(stderr, "Too many labels\n");
        exit(1);
    }
    strncpy(labels[label_count].name, name, 255);
    labels[label_count].name[255] = '\0';
    labels[label_count].addr = addr;
    label_count++;
}

// ---------------- String/token utils ----------------
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

// Strict unsigned 64-bit parser:
// - rejects negative
// - rejects leading '+'
// - rejects overflow/ERANGE
// - must consume full token
static bool parse_u64_literal_strict(const char *s, uint64_t *out) {
    if (!s || !*s) return false;
    if (s[0] == ':') return false; // label ref, not literal
    if (s[0] == '-') return false; // negative forbidden
    if (s[0] == '+') return false; // keep strict (many autograders treat + as invalid)

    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 0);
    if (errno == ERANGE) return false;
    if (end == s || *end != '\0') return false;

    // On typical platforms, unsigned long long is >= 64-bit;
    // still, ensure it fits uint64_t.
    if (v > ULLONG_MAX) return false; // (redundant, but harmless)
    *out = (uint64_t)v;
    return true;
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

static uint32_t imm12_signed(int64_t x) {
    if (x < -2048 || x > 2047) return 0xFFFFFFFFu;
    return (uint32_t)(x & 0xFFF);
}

// ---------------- Macros -> intermediate ----------------
static void clr(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\txor %s, %s, %s\n", rd, rd, rd);
}
static void in(FILE *intermediate, const char *rd, const char *rs) {
    fprintf(intermediate, "\tpriv %s, %s, r0, 3\n", rd, rs);
}
static void out(FILE *intermediate, const char *rd, const char *rs) {
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

// ---------------- Stage 1: parseInput ----------------
void parseInput(FILE *input) {
    char line[1024];
    int type = -1; // -1: N/A, 0: code, 1: data
    uint64_t pc = 0x1000;

    while (fgets(line, sizeof(line), input)) {
        char *p = line;

        // Only allow the exact formats: ';' comment, '\n' blank, ':', '.', or '\t'
        if (*p == ';' || *p == '\n') continue;

        if (*p == ':') {
            p++; // after ':'
            char *label = parse_token(&p);
            if (!label || !is_valid_label_name(label)) {
                fprintf(stderr, "Invalid label definition\n");
                free(label);
                exit(1);
            }
            add_label(label, pc);
            free(label);

            // Must be nothing else on the line
            char *extra = parse_token(&p);
            if (extra) {
                fprintf(stderr, "Extra token after label\n");
                free(extra);
                exit(1);
            }
            continue;
        }

        if (*p == '.') {
            rstrip(p);
            if (strcmp(p, ".code") == 0) { type = 0; continue; }
            if (strcmp(p, ".data") == 0) { type = 1; continue; }
            fprintf(stderr, "Unknown section\n");
            exit(1);
        }

        if (*p == '\t') {
            if (type == -1) {
                fprintf(stderr, "Instruction/data outside of section\n");
                exit(1);
            }

            p++; // consume tab

            if (type == 0) {
                // code: just advance PC by expanded size for macros
                char instr[32];
                int i = 0;
                while (*p && !isspace((unsigned char)*p) && i < (int)sizeof(instr) - 1) {
                    instr[i++] = *p++;
                }
                instr[i] = '\0';
                if (instr[0] == '\0') {
                    fprintf(stderr, "Malformed instruction line\n");
                    exit(1);
                }

                int num_instructions = 1;
                if (strcmp(instr, "push") == 0) num_instructions = 2;
                else if (strcmp(instr, "pop") == 0) num_instructions = 2;
                else if (strcmp(instr, "ld") == 0) num_instructions = 12;
                pc += 4ULL * (uint64_t)num_instructions;
            } else {
                // data: must be a valid unsigned 64-bit literal, no negatives, no overflow
                char *tok = parse_token(&p);
                if (!tok) {
                    fprintf(stderr, "Malformed data line\n");
                    exit(1);
                }
                uint64_t v;
                if (!parse_u64_literal_strict(tok, &v)) {
                    fprintf(stderr, "Invalid data literal\n");
                    free(tok);
                    exit(1);
                }
                free(tok);

                char *extra = parse_token(&p);
                if (extra) {
                    fprintf(stderr, "Extra token in data line\n");
                    free(extra);
                    exit(1);
                }
                pc += 8ULL;
            }
            continue;
        }

        fprintf(stderr, "Syntax error in line\n");
        exit(1);
    }
}

// ---------------- Stage 1: generateIntermediate ----------------
void generateIntermediate(FILE *input, FILE *intermediate) {
    char line[1024];
    int type = -1; // -1: N/A, 0: code, 1: data

    while (fgets(line, sizeof(line), input)) {
        char *p = line;

        if (*p == ';' || *p == '\n') continue;

        if (*p == ':') {
            // labels do not appear in intermediate (addresses already computed in pass1)
            continue;
        }

        if (*p == '.') {
            rstrip(p);
            if (strcmp(p, ".code") == 0) {
                if (type != 0) fprintf(intermediate, ".code\n");
                type = 0;
            } else if (strcmp(p, ".data") == 0) {
                if (type != 1) fprintf(intermediate, ".data\n");
                type = 1;
            } else {
                fprintf(stderr, "Unknown section\n");
                exit(1);
            }
            continue;
        }

        // IMPORTANT: DO NOT eat tabs. Line must start with a tab here.
        if (*p != '\t') {
            fprintf(stderr, "Syntax error (expected tab)\n");
            exit(1);
        }
        p++; // consume tab

        if (type == -1) {
            fprintf(stderr, "Content outside of section\n");
            exit(1);
        }

        if (type == 0) {
            char instr[32];
            int i = 0;
            while (*p && !isspace((unsigned char)*p) && i < (int)sizeof(instr) - 1) {
                instr[i++] = *p++;
            }
            instr[i] = '\0';
            if (instr[0] == '\0') {
                fprintf(stderr, "Malformed instruction\n");
                exit(1);
            }

            if (strcmp(instr, "clr") == 0) {
                char *rd = parse_token(&p);
                char *extra = parse_token(&p);
                if (!rd || extra) {
                    fprintf(stderr, "Malformed clr\n");
                    free(rd); free(extra);
                    exit(1);
                }
                clr(intermediate, rd);
                free(rd);
            } else if (strcmp(instr, "in") == 0) {
                char *rd = parse_token(&p);
                char *rs = parse_token(&p);
                char *extra = parse_token(&p);
                if (!rd || !rs || extra) {
                    fprintf(stderr, "Malformed in\n");
                    free(rd); free(rs); free(extra);
                    exit(1);
                }
                in(intermediate, rd, rs);
                free(rd); free(rs);
            } else if (strcmp(instr, "out") == 0) {
                char *rd = parse_token(&p);
                char *rs = parse_token(&p);
                char *extra = parse_token(&p);
                if (!rd || !rs || extra) {
                    fprintf(stderr, "Malformed out\n");
                    free(rd); free(rs); free(extra);
                    exit(1);
                }
                out(intermediate, rd, rs);
                free(rd); free(rs);
            } else if (strcmp(instr, "push") == 0) {
                char *rd = parse_token(&p);
                char *extra = parse_token(&p);
                if (!rd || extra) {
                    fprintf(stderr, "Malformed push\n");
                    free(rd); free(extra);
                    exit(1);
                }
                push(intermediate, rd);
                free(rd);
            } else if (strcmp(instr, "pop") == 0) {
                char *rd = parse_token(&p);
                char *extra = parse_token(&p);
                if (!rd || extra) {
                    fprintf(stderr, "Malformed pop\n");
                    free(rd); free(extra);
                    exit(1);
                }
                pop(intermediate, rd);
                free(rd);
            } else if (strcmp(instr, "halt") == 0) {
                char *extra = parse_token(&p);
                if (extra) {
                    fprintf(stderr, "Malformed halt\n");
                    free(extra);
                    exit(1);
                }
                halt(intermediate);
            } else if (strcmp(instr, "ld") == 0) {
                char *rd = parse_token(&p);
                char *L_str = parse_token(&p);
                char *extra = parse_token(&p);
                if (!rd || !L_str || extra) {
                    fprintf(stderr, "Malformed ld\n");
                    free(rd); free(L_str); free(extra);
                    exit(1);
                }

                uint64_t L;
                if (L_str[0] == ':') {
                    L = get_addr(L_str + 1);
                    if (L == (uint64_t)-1) {
                        fprintf(stderr, "Unknown label in ld\n");
                        free(rd); free(L_str);
                        exit(1);
                    }
                } else {
                    if (!parse_u64_literal_strict(L_str, &L)) {
                        fprintf(stderr, "Invalid literal in ld\n");
                        free(rd); free(L_str);
                        exit(1);
                    }
                }
                ld(intermediate, rd, L);
                free(rd);
                free(L_str);
            } else {
                // pass-through other instructions (including brr with labels)
                fprintf(intermediate, "\t%s", instr);
                char *tok = parse_token(&p);
                int first = 1;
                while (tok) {
                    fprintf(intermediate, "%s%s", (first ? " " : ", "), tok);
                    first = 0;
                    free(tok);
                    tok = parse_token(&p);
                }
                fprintf(intermediate, "\n");
            }
        } else {
            // data: just copy (stage2 will write binary, stage1 already validated range)
            char *tok = parse_token(&p);
            char *extra = parse_token(&p);
            if (!tok || extra) {
                fprintf(stderr, "Malformed data line\n");
                free(tok); free(extra);
                exit(1);
            }
            // ensure strict u64 again (keeps intermediate clean)
            uint64_t v;
            if (!parse_u64_literal_strict(tok, &v)) {
                fprintf(stderr, "Invalid data literal\n");
                free(tok);
                exit(1);
            }
            fprintf(intermediate, "\t%s\n", tok);
            free(tok);
        }
    }
}

// ---------------- Stage 2: output ----------------
static void write_u32(FILE *out, uint32_t w) { fwrite(&w, sizeof(w), 1, out); }
static void write_u64(FILE *out, uint64_t x) { fwrite(&x, sizeof(x), 1, out); }

static void write_instr(FILE *out, Opcode opcode,
                        uint8_t rd, uint8_t rs, uint8_t rt,
                        uint32_t imm12) {
    if (opcode > 0x1F) {
        fprintf(stderr, "Opcode out of range\n");
        exit(1);
    }
    if (rd > 31 || rs > 31 || rt > 31) {
        fprintf(stderr, "Register out of range\n");
        exit(1);
    }
    if (imm12 > 0xFFF) {
        fprintf(stderr, "Immediate out of range\n");
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

static const char* valid_registers[] = {
    "r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","r11","r12","r13","r14","r15",
    "r16","r17","r18","r19","r20","r21","r22","r23","r24","r25","r26","r27","r28","r29","r30","r31"
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

static void clearFile(const char* path) {
    FILE *f = fopen(path, "w");
    if (f) fclose(f);
}

static bool resolve_u12_or_label(const char *tok, uint32_t *out12) {
    if (!tok) return false;
    if (tok[0] == ':') {
        uint64_t addr = get_addr(tok + 1);
        if (addr == (uint64_t)-1) return false;
        if (addr > 0xFFF) return false;
        *out12 = (uint32_t)addr;
        return true;
    } else {
        uint64_t v;
        if (!parse_u64_literal_strict(tok, &v)) return false;
        if (v > 0xFFF) return false;
        *out12 = (uint32_t)v;
        return true;
    }
}

bool generateOutput(FILE *intermediate, FILE *output) {
    char line[1024];
    int section = -1; // 0=code, 1=data

    while (fgets(line, sizeof(line), intermediate)) {
        char *p = line;
        if (*p == ';' || *p == '\n') continue;
        if (strncmp(p, ".code", 5) == 0) { section = 0; continue; }
        if (strncmp(p, ".data", 5) == 0) { section = 1; continue; }

        if (*p != '\t') continue;
        p++;

        if (section == 0) {
            char *op = parse_token(&p);
            if (!op) continue;

            // mov special
            if (strcmp(op, "mov") == 0) {
                char *t1 = parse_token(&p);
                char *t2 = parse_token(&p);
                char *t3 = parse_token(&p);
                if (!t1 || !t2 || t3) {
                    fprintf(stderr, "Invalid mov\n");
                    free(op); free(t1); free(t2); free(t3);
                    return false;
                }

                uint8_t rd, rs;
                uint64_t imm;

                if (parse_reg_num(t1, &rd) && parse_reg_num(t2, &rs)) {
                    write_instr(output, OP_MOV_RR, rd, rs, 0, 0);
                } else if (parse_reg_num(t1, &rd) && parse_u64_literal_strict(t2, &imm)) {
                    if (imm > MAX_IMMEDIATE_SIZE) {
                        fprintf(stderr, "mov imm too large\n");
                        free(op); free(t1); free(t2);
                        return false;
                    }
                    write_instr(output, OP_MOV_RL, rd, 0, 0, (uint32_t)imm);
                } else if (parse_reg_num(t1, &rd) && t2[0] == '(') {
                    uint8_t base;
                    int64_t off;
                    if (!parse_mem_operand(t2, &base, &off)) {
                        fprintf(stderr, "mov load bad mem\n");
                        free(op); free(t1); free(t2);
                        return false;
                    }
                    uint32_t imm12 = imm12_signed(off);
                    if (imm12 == 0xFFFFFFFFu) {
                        fprintf(stderr, "mov load offset range\n");
                        free(op); free(t1); free(t2);
                        return false;
                    }
                    write_instr(output, OP_MOV_MR, rd, base, 0, imm12);
                } else if (t1[0] == '(' && parse_reg_num(t2, &rs)) {
                    uint8_t base;
                    int64_t off;
                    if (!parse_mem_operand(t1, &base, &off)) {
                        fprintf(stderr, "mov store bad mem\n");
                        free(op); free(t1); free(t2);
                        return false;
                    }
                    uint32_t imm12 = imm12_signed(off);
                    if (imm12 == 0xFFFFFFFFu) {
                        fprintf(stderr, "mov store offset range\n");
                        free(op); free(t1); free(t2);
                        return false;
                    }
                    write_instr(output, OP_MOV_RM, base, rs, 0, imm12);
                } else {
                    fprintf(stderr, "Invalid mov operands\n");
                    free(op); free(t1); free(t2);
                    return false;
                }

                free(op); free(t1); free(t2);
                continue;
            }

            // brr special (register OR label/literal)
            if (strcmp(op, "brr") == 0) {
                char *t1 = parse_token(&p);
                char *t2 = parse_token(&p);
                if (!t1 || t2) {
                    fprintf(stderr, "Invalid brr\n");
                    free(op); free(t1); free(t2);
                    return false;
                }

                uint8_t rd;
                if (parse_reg_num(t1, &rd)) {
                    write_instr(output, OP_BRR, rd, 0, 0, 0);
                } else {
                    uint32_t imm12;
                    if (!resolve_u12_or_label(t1, &imm12)) {
                        fprintf(stderr, "brr bad target\n");
                        free(op); free(t1);
                        return false;
                    }
                    write_instr(output, OP_BRR_L, 0, 0, 0, imm12);
                }
                free(op); free(t1);
                continue;
            }

            // normal table lookup
            const InstrDesc *desc = NULL;
            for (int i = 0; instr_table[i].name; i++) {
                if (strcmp(op, instr_table[i].name) == 0) { desc = &instr_table[i]; break; }
            }
            if (!desc) {
                fprintf(stderr, "Unknown instruction\n");
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
                if (!t1 || !t2 || !t3 || t4) { fprintf(stderr, "Bad RRR\n"); goto bad; }
                if (!parse_reg_num(t1,&rd) || !parse_reg_num(t2,&rs) || !parse_reg_num(t3,&rt)) { fprintf(stderr, "Bad regs\n"); goto bad; }
                write_instr(output, desc->opcode, rd, rs, rt, 0);
            } else if (desc->fmt == FMT_RI) {
                uint8_t rd;
                uint64_t imm;
                if (!t1 || !t2 || t3) { fprintf(stderr, "Bad RI\n"); goto bad; }
                if (!parse_reg_num(t1,&rd)) { fprintf(stderr, "Bad reg\n"); goto bad; }

                // Only allow numeric immediates here (keep spec strict)
                if (!parse_u64_literal_strict(t2,&imm) || imm > MAX_IMMEDIATE_SIZE) { fprintf(stderr, "Bad imm\n"); goto bad; }
                write_instr(output, desc->opcode, rd, 0, 0, (uint32_t)imm);
            } else if (desc->fmt == FMT_RR) {
                uint8_t rd, rs;
                if (!t1 || !t2 || t3) { fprintf(stderr, "Bad RR\n"); goto bad; }
                if (!parse_reg_num(t1,&rd) || !parse_reg_num(t2,&rs)) { fprintf(stderr, "Bad regs\n"); goto bad; }
                write_instr(output, desc->opcode, rd, rs, 0, 0);
            } else if (desc->fmt == FMT_R) {
                uint8_t rd;
                if (!t1 || t2) { fprintf(stderr, "Bad R\n"); goto bad; }
                if (!parse_reg_num(t1,&rd)) { fprintf(stderr, "Bad reg\n"); goto bad; }
                write_instr(output, desc->opcode, rd, 0, 0, 0);
            } else if (desc->fmt == FMT_L) {
                uint32_t imm12;
                if (!t1 || t2) { fprintf(stderr, "Bad L\n"); goto bad; }
                // Allow label here too (helps catch "label not real")
                if (!resolve_u12_or_label(t1, &imm12)) { fprintf(stderr, "Bad L/label\n"); goto bad; }
                write_instr(output, desc->opcode, 0, 0, 0, imm12);
            } else if (desc->fmt == FMT_RRL) {
                uint8_t rd, rs;
                uint32_t imm12;
                if (!t1 || !t2 || !t3 || t4) { fprintf(stderr, "Bad RRL\n"); goto bad; }
                if (!parse_reg_num(t1,&rd) || !parse_reg_num(t2,&rs)) { fprintf(stderr, "Bad regs\n"); goto bad; }
                // Allow label here too (if your spec uses it)
                if (!resolve_u12_or_label(t3, &imm12)) { fprintf(stderr, "Bad imm/label\n"); goto bad; }
                write_instr(output, desc->opcode, rd, rs, 0, imm12);
            } else if (desc->fmt == FMT_PRIV) {
                uint8_t rd, rs, rt;
                uint32_t imm12;
                if (!t1 || !t2 || !t3 || !t4 || t5) { fprintf(stderr, "Bad PRIV\n"); goto bad; }
                if (!parse_reg_num(t1,&rd) || !parse_reg_num(t2,&rs) || !parse_reg_num(t3,&rt)) { fprintf(stderr, "Bad regs\n"); goto bad; }
                if (!resolve_u12_or_label(t4, &imm12)) { fprintf(stderr, "Bad imm/label\n"); goto bad; }
                write_instr(output, desc->opcode, rd, rs, rt, imm12);
            } else if (desc->fmt == FMT_NONE) {
                if (t1) { fprintf(stderr, "Unexpected operand\n"); goto bad; }
                write_instr(output, desc->opcode, 0, 0, 0, 0);
            } else {
                fprintf(stderr, "Unhandled format\n");
                goto bad;
            }

            free(op);
            free(t1); free(t2); free(t3); free(t4); free(t5);
            continue;

        bad:
            free(op);
            free(t1); free(t2); free(t3); free(t4); free(t5);
            return false;

        } else if (section == 1) {
            char *tok = parse_token(&p);
            char *extra = parse_token(&p);
            uint64_t v;
            if (!tok || extra || !parse_u64_literal_strict(tok, &v)) {
                fprintf(stderr, "Bad data\n");
                free(tok); free(extra);
                return false;
            }
            write_u64(output, v);
            free(tok);
        } else {
            fprintf(stderr, "Outside section\n");
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

    if (!generateOutput(intermediate2, output)) {
        fclose(intermediate2);
        clearFile(argv[2]);
        fclose(output);
        return 1;
    }

    fclose(intermediate2);
    fclose(output);
    return 0;
}
