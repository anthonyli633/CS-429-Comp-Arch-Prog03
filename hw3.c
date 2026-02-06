#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>

#define MAX_LABELS 1024
#define MAX_REGISTER_SIZE 0b11111 // 5 bits for register numbers
#define MAX_IMMEDIATE_SIZE 0xFFF // 12 bits for immediate values (for RI format)

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
    FMT_PRIV,   // rd, rs, rt, L
    FMT_NONE    // no operands
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
    { "not",    FMT_RR,  OP_NOT  },   // not rd, rs
    { "shftr",  FMT_RRR, OP_SHFTR  },  // shftr rd, rs, rt
    { "shftri", FMT_RI,  OP_SHFTRI },  // shftri rd, L
    { "shftl",  FMT_RRR, OP_SHFTL  },  // shftl rd, rs, rt
    { "shftli", FMT_RI,  OP_SHFTLI },  // shftli rd, L
    { "br",     FMT_R,   OP_BR     },  // br rd
    { "brr",    FMT_R,   OP_BRR    },  // brr rd
    { "brr",    FMT_L,   OP_BRR_L  },  // brr L
    { "brnz",   FMT_RR,  OP_BRNZ   },  // brnz rd, rs   (adjust if your spec differs)
    { "call",   FMT_R,   OP_CALL   },  // call rd
    { "return", FMT_NONE,   OP_RETURN },  // return rd  (if your spec uses no operands, change to FMT_L/none)
    { "brgt",   FMT_RRR, OP_BRGT   },  // brgt rd, rs, rt (adjust if your spec differs)
    { "priv",   FMT_PRIV, OP_PRIV  },  // priv rd, rs, rt, L
    { "addf",   FMT_RRR, OP_ADDF },
    { "subf",   FMT_RRR, OP_SUBF },
    { "mulf",   FMT_RRR, OP_MULF },
    { "divf",   FMT_RRR, OP_DIVF },
    { NULL,     0,       0},
};


// Labels
typedef struct {
    char name[64];
    uint64_t addr;
} Label;

static Label labels[MAX_LABELS];
static int label_count = 0;

uint64_t get_addr(const char *label) {
    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, label) == 0) {
            return labels[i].addr;
        }
    } return 0;
}
void add_label(const char *name, uint64_t addr) {
    strncpy(labels[label_count].name, name, 63);
    labels[label_count].name[63] = '\0';
    labels[label_count].addr = addr;
    label_count++;
}

// String utils
void rstrip(char *s) {
    size_t n = strlen(s);
    while (n > 0 && isspace((unsigned char)s[n - 1])) s[--n] = '\0';
}
void strip(char *s) {
    char *p = s;
    while (*p && isspace((unsigned char)*p)) p++;
    memmove(s, p, strlen(p) + 1);
    rstrip(s);
}
char *my_strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *p = malloc(len);
    if (p) memcpy(p, s, len);
    return p;
}
char* parse_token(char **p) {
    while (**p && (isspace((unsigned char)**p) || **p == ',')) (*p)++;
    if (**p == '\0') return NULL;
    char token[100];
    int i = 0;
    while (**p && !isspace((unsigned char)**p) && **p != ',') {
        if (i < 99) token[i++] = **p;
        (*p)++;
    }
    token[i] = '\0';
    return my_strdup(token);
}
bool parse_u64_literal(const char *s, uint64_t *out) {
    if (!s || !*s) return false;
    if (s[0] == ':') return false; // label, not literal
    if (s[0] == '-') return false; // no signed literals

    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 0); // base 0 supports 0x...
    if (errno != 0 || end == s || *end != '\0') return false;
    *out = (uint64_t)v;
    return true;
}
bool parse_mem_operand(const char *tok, uint8_t *base, int64_t *off) {
    if (!tok || !base || !off) return false;
    const char *p = tok;
    if (*p != '(') return false;
    p++;
    if (*p != 'r') return false;
    p++;
    char *end = NULL;
    errno = 0;
    long reg = strtol(p, &end, 10);
    if (errno != 0 || end == p || *end != ')' || reg < 0 || reg > 31)
        return false;
    *base = (uint8_t)reg;
    p = end + 1;
    if (*p != '(') return false;
    p++;
    errno = 0;
    long long offset = strtoll(p, &end, 0);
    if (errno != 0 || end == p || *end != ')')
        return false;
    p = end + 1;
    if (*p != '\0') return false;

    *off = (int64_t)offset;
    return true;
}
uint32_t imm12_signed(int64_t x) {
    if (x < -2048 || x > 2047)
        return 0xFFFFFFFFu;   // out of range
    return (uint32_t)(x & 0xFFF);  // two’s complement, low 12 bits
}

// Evaluate Macros
void clr(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\txor %s, %s, %s\n", rd, rd, rd);
}
void in(FILE *intermediate, const char *rd, const char *rs) {
    fprintf(intermediate, "\tpriv %s, %s, r0, 3\n", rd, rs);
}
void out(FILE *intermediate, const char *rd, const char *rs) {
    fprintf(intermediate, "\tpriv %s, %s, r0, 4\n", rd, rs);
}
void push(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\tmov (r31)(-8), %s\n", rd);
    fprintf(intermediate, "\tsubi r31, 8\n");
}
void pop(FILE *intermediate, const char *rd) {
    fprintf(intermediate, "\tmov %s, (r31)(0)\n", rd);
    fprintf(intermediate, "\taddi r31, 8\n");
}
void halt(FILE *intermediate) {
    fprintf(intermediate, "\tpriv r0, r0, r0, 0\n");
}
void ld(FILE *intermediate, const char *rd, uint64_t L) {
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
    char line[1024];
    int type = -1; // -1: N/A, 0: code, 1: data

    uint64_t pc = 0x1000;

    while (fgets(line, sizeof(line), input)) {
        char *p = line;
        if (*p == ';' || *p == '\n') continue;
        else if (*p == ':') {
            // Check valid label (< 256 chars, nonempty, no spaces)
            rstrip(p + 1);
            if (strlen(p + 1) == 0 || strlen(p + 1) > 255 || strchr(p + 1, ' ')) {
                fprintf(stderr, "Invalid label: %s\n", p + 1);
                exit(1);
            }
            add_label(p + 1, pc);
            printf("Added label: %s at address 0x%lX\n", p + 1, pc);
        } else if (*p == '.') {
            rstrip(p);
            // check if .code and nothing else after
            if (strncmp(p, ".code", 5) == 0 && p[5] == '\0') { type = 0; }
            else if (strncmp(p, ".data", 5) == 0 && p[5] == '\0') { type = 1; }
            else { fprintf(stderr, "Unknown section\n"); exit(1); }
        } else if (*p == '\t') {
            if (type == -1) { fprintf(stderr, "Instruction outside of .code/.data section\n"); exit(1); }
            p++;
            if (type == 0) {
                char instr[16];
                int i = 0;
                while (*p && !isspace((unsigned char)*p) && i < (int)sizeof(instr)-1) instr[i++] = *p++;
                instr[i] = '\0';

                int num_instructions = 1;
                if (strcmp(instr, "push") == 0) num_instructions = 2;
                else if (strcmp(instr, "pop") == 0) num_instructions = 2;  
                else if (strcmp(instr, "ld") == 0) num_instructions = 12;
                pc += 4ULL * num_instructions;
            } else {
                // check if valid data (64 bit unsigned integer)
                char *tok = parse_token(&p);
                if (!tok) { fprintf(stderr, "Malformed data line\n"); exit(1); }
                uint64_t v;
                if (!parse_u64_literal(tok, &v)) {
                    fprintf(stderr, "Invalid data literal: %s\n", tok);
                    free(tok);
                    exit(1);
                }
                free(tok);
                pc += 8ULL;
            }
        } else {
            fprintf(stderr, "Syntax error in line: %s", line); exit(1);
        }
    } 
}

void generateIntermediate(FILE *input, FILE *intermediate) {
    char line[1024];
    int type = -1; // -1: N/A, 0: code, 1: data
    while (fgets(line, sizeof(line), input)) {
        char *p = line;
        if (*p == ';' || *p == '\n') continue;
        else if (*p == ':') {
            continue;
        } else if (*p == '.') {
            if (strncmp(p, ".code", 5) == 0) { 
                if (type != 0) fprintf(intermediate, ".code\n");
                type = 0;
            }
            else if (strncmp(p, ".data", 5) == 0) { 
                if (type != 1) fprintf(intermediate, ".data\n");
                type = 1;
            }
            continue;
        } 
        
        p++;
        while (*p && isspace((unsigned char)*p)) p++;
        if (type == 0) {
            char instr[16];
            int i = 0;
            while (*p && !isspace((unsigned char)*p) && i < (int)sizeof(instr)-1) instr[i++] = *p++;
            instr[i] = '\0';

            if (strcmp(instr, "clr") == 0) {
                char *rd = parse_token(&p);
                if (!rd) { fprintf(stderr, "Malformed clr\n"); exit(1); }
                clr(intermediate, rd);
                free(rd);
            } else if (strcmp(instr, "in") == 0) {
                char *rd = parse_token(&p);
                char *rs = parse_token(&p);
                if (!rd) { fprintf(stderr, "Malformed in\n"); exit(1); }
                in(intermediate, rd, rs);
                free(rd); free(rs);
            } else if (strcmp(instr, "out") == 0) {
                char *rd = parse_token(&p);
                char *rs = parse_token(&p);
                if (!rd || !rs) { fprintf(stderr, "Malformed out\n"); exit(1); }
                out(intermediate, rd, rs);
                free(rd); free(rs);
            } else if (strcmp(instr, "push") == 0) {
                char *rd = parse_token(&p);
                if (!rd) { fprintf(stderr, "Malformed push\n"); exit(1); }
                push(intermediate, rd);
                free(rd);
            } else if (strcmp(instr, "pop") == 0) {
                char *rd = parse_token(&p);
                if (!rd) { fprintf(stderr, "Malformed pop\n"); exit(1); }
                pop(intermediate, rd);
                free(rd);
            } else if (strcmp(instr, "halt") == 0) {
                halt(intermediate);
            } else if (strcmp(instr, "ld") == 0) {
                char *rd = parse_token(&p);
                char *L_str = parse_token(&p);
                if (!rd || !L_str) { fprintf(stderr, "Malformed ld\n"); exit(1); }

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
                ld(intermediate, rd, L);
                free(rd);
                free(L_str);
            } else {
                char* token = parse_token(&p);; 
                int first = 1;
                if (strcmp(instr, "brr") == 0) {
                    if (!token) { fprintf(stderr, "Malformed brr\n"); exit(1); }
                    if (token[0] == ':') {
                        fprintf(stderr, "brr address out of range: %s\n", token);
                        free(token);
                        exit(1);
                    } 
                }
                fprintf(intermediate, "\t%s", instr);
                while (token) {
                    fprintf(intermediate, "%s%s", (first ? " " : ", "), token);
                    first = 0;
                    free(token);
                    token = parse_token(&p);
                }
                fprintf(intermediate, "\n");
            }
        } else {
            char *tok = parse_token(&p);
            if (!tok) { fprintf(stderr, "Malformed data line\n"); exit(1); }
            fprintf(intermediate, "\t%s\n", tok);
            free(tok);
        }
    } 
}

static void write_u32(FILE *out, uint32_t w) {
    fwrite(&w, sizeof(w), 1, out);
}
static void write_u64(FILE *out, uint64_t x) {
    fwrite(&x, sizeof(x), 1, out);
}
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

static char* valid_registers [] = {
    "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7",
    "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
    "r16", "r17", "r18", "r19", "r20", "r21", "r22", "r23",
    "r24", "r25", "r26", "r27", "r28", "r29", "r30", "r31"
};
static bool parse_reg_num(const char *tok, uint8_t *out) {
    for (int i = 0; i < 32; i++) {
        if (strcmp(tok, valid_registers[i]) == 0) {
            *out = (uint8_t)i;
            return true;
        }
    } return false;
}

void clearFile(const char* path) {
    FILE *f = fopen(path, "w");
    fclose(f);
}

bool generateOutput(FILE *intermediate, FILE *output) {
    char line[1024];
    int section = -1; // 0 = code, 1 = data
    printf("Generating output...\n");

    while (fgets(line, sizeof(line), intermediate)) {
        printf("Processing line: %s", line);
        char *p = line;
        if (*p == ';' || *p == '\n') continue;
        if (strncmp(p, ".code", 5) == 0) { section = 0; continue; }
        if (strncmp(p, ".data", 5) == 0) { section = 1; continue; }
        
        if (*p != '\t') continue;
        p++;

        if (section == 0) {
            char *op = parse_token(&p);
            if (!op) continue;

            // Multiple parameters
            if (strcmp(op, "mov") == 0) {
                char *t1 = parse_token(&p);
                char *t2 = parse_token(&p);
                char *t3 = parse_token(&p);
                if (!t1 || !t2 || t3) {
                    fprintf(stderr, "Invalid mov instruction: %s\n", line);
                    free(t1); free(t2); free(t3); free(op);
                    return 0;
                }

                uint8_t rd, rs;
                uint64_t imm;

                // mov rd, rs
                if (parse_reg_num(t1, &rd) && parse_reg_num(t2, &rs)) {
                    write_instr(output, OP_MOV_RR, rd, rs, 0, 0);
                }
                // mov rd, L
                else if (parse_reg_num(t1, &rd) && parse_u64_literal(t2, &imm)) {
                    if (imm > MAX_IMMEDIATE_SIZE) {
                        fprintf(stderr, "Immediate too large for mov rd, L: %s\n", line);
                        free(t1); free(t2); free(op);
                        return 0;
                    }
                    write_instr(output, OP_MOV_RL, rd, 0, 0, (uint32_t)imm);
                }
                // mov rd, (rs)(L)   (load)
                else if (parse_reg_num(t1, &rd) && t2[0] == '(' && t2[strlen(t2) - 1] == ')') {
                    uint8_t base;
                    int64_t off;

                    if (!parse_mem_operand(t2, &base, &off)) {
                        fprintf(stderr, "Invalid memory operand for mov rd,(rs)(L): %s\n", line);
                        free(t1); free(t2); free(op);
                        return 0;
                    }

                    uint32_t imm12 = imm12_signed(off);
                    if (imm12 == 0xFFFFFFFFu) {
                        fprintf(stderr, "mov offset out of signed 12-bit range: %lld\n", (long long)off);
                        free(t1); free(t2); free(op);
                        return 0;
                    }

                    // Convention: opcode OP_MOV_MR, rd=dest, rs=base, imm=offset
                    write_instr(output, OP_MOV_MR, rd, base, 0, imm12);
                }
                // mov (rd)(L), rs   (store)
                else if (t1[0] == '(' && t1[strlen(t1) - 1] == ')' && parse_reg_num(t2, &rs)) {
                    uint8_t base;
                    int64_t off;

                    if (!parse_mem_operand(t1, &base, &off)) {
                        fprintf(stderr, "Invalid memory operand for mov (rd)(L),rs: %s\n", line);
                        free(t1); free(t2); free(op);
                        return 0;
                    }

                    uint32_t imm12 = imm12_signed(off);
                    if (imm12 == 0xFFFFFFFFu) {
                        fprintf(stderr, "mov offset out of signed 12-bit range: %lld\n", (long long)off);
                        free(t1); free(t2); free(op);
                        return 0;
                    }

                    // Convention: opcode OP_MOV_RM, rd=base, rs=src, imm=offset
                    write_instr(output, OP_MOV_RM, base, rs, 0, imm12);
                }
                else {
                    fprintf(stderr, "Invalid mov operands: %s\n", line);
                    free(t1); free(t2); free(op);
                    return 0;
                }

                free(t1);
                free(t2);
                free(op);
                continue;
            }

            if (strcmp(op, "brr") == 0) {
                char *t1 = parse_token(&p);
                char *t2 = parse_token(&p);
                if (!t1 || t2) {
                    fprintf(stderr, "Invalid arguments for brr: %s\n", line);
                    free(t1); free(t2);
                    free(op);
                    return 0;
                }
                // brr rd
                uint8_t rd;
                uint64_t imm;
                if (parse_reg_num(t1, &rd)) {
                    write_instr(output, OP_BRR, rd, 0, 0, 0);
                } 
                // brr :LABEL
                else if (t1[0] == ':') {
                    uint64_t addr = get_addr(t1 + 1);
                    if (addr > 0xFFF) {  // because your encoder only has imm12
                        fprintf(stderr, "brr out of 12-bit range\n");
                        free(t1); free(op);
                        return 0;
                    }
                    write_instr(output, OP_BRR_L, 0, 0, 0, (uint32_t)addr);
                }
                // brr literal (e.g. 123 or 0x1A0)
                else if (parse_u64_literal(t1, &imm)) {
                    if (imm > 0xFFF) {
                        fprintf(stderr, "brr out of 12-bit range\n");
                        free(t1); free(op);
                        return 0;
                    }
                    write_instr(output, OP_BRR_L, 0, 0, 0, (uint32_t)imm);
                }
                else {
                    fprintf(stderr, "Invalid operand for brr: %s\n", t1);
                    free(t1); free(op);
                    return 0;
                }
                continue;
            }

            const InstrDesc *desc = NULL;
            for (int i = 0; instr_table[i].name; i++) {
                if (strcmp(op, instr_table[i].name) == 0) { desc = &instr_table[i]; break; }
            }
            if (!desc) {
                fprintf(stderr, "Unknown instruction in intermediate: %s\n", op);
                free(op);
                return 0;
            }

            char *t1 = parse_token(&p);
            char *t2 = parse_token(&p);
            char *t3 = parse_token(&p);
            char *t4 = parse_token(&p);
            char *t5 = parse_token(&p);

            if (desc->fmt == FMT_RRR) {
                uint8_t rd, rs, rt;
                if (!t1 || !t2 || !t3 || t4) {
                    fprintf(stderr, "Bad RRR format: %s\n", line);
                    free(t1); free(t2); free(t3); free(t4); free(op);
                    return 0;
                }
                if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs) || !parse_reg_num(t3, &rt)) {
                    fprintf(stderr, "Bad RRR operands: %s\n", line);
                    return 0;
                }
                write_instr(output, desc->opcode, rd, rs, rt, 0);
            }
            else if (desc->fmt == FMT_RI) {
                uint8_t rd;
                uint64_t imm;
                if (!t1 || !t2 || t3) {
                    fprintf(stderr, "Bad RI format: %s\n", line);
                    free(t1); free(t2); free(t3); free(t4); free(op);
                    return 0;
                }
                if (!parse_reg_num(t1, &rd) || !parse_u64_literal(t2, &imm) || imm > MAX_IMMEDIATE_SIZE) {
                    fprintf(stderr, "Bad RI operands / imm too large: %s\n", line);
                    return 0;
                }
                write_instr(output, desc->opcode, rd, 0, 0, (uint32_t)imm); // NOTE: depends on exact spec for addi/shftli
            }
            else if (desc->fmt == FMT_RR) {
                uint8_t rd, rs;
                if (!t1 || !t2 || t3) {
                    fprintf(stderr, "Bad RR format: %s\n", line);
                    free(t1); free(t2); free(t3); free(t4); free(op);
                    return 0;
                }
                if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs)) {
                    fprintf(stderr, "Bad RR operands: %s\n", line);
                    return 0;
                }
                write_instr(output, desc->opcode, rd, rs, 0, 0);
            }
            else if (desc->fmt == FMT_R) {
                uint8_t rd;
                if (!t1 || t2) {
                    fprintf(stderr, "Bad R format: %s\n", line);
                    free(t1); free(t2); free(t3); free(t4); free(op);
                    return 0;
                }
                if (!parse_reg_num(t1, &rd)) {
                    fprintf(stderr, "Bad R operand: %s\n", line);
                    return 0;
                }
                write_instr(output, desc->opcode, rd, 0, 0, 0);
            }
            else if (desc->fmt == FMT_L) {
                uint64_t imm;
                if (!t1 || t2) {
                    fprintf(stderr, "Bad L format: %s\n", line);
                    free(t1); free(t2); free(t3); free(t4); free(op);
                    return 0;
                }
                if (!parse_u64_literal(t1, &imm) || imm > MAX_IMMEDIATE_SIZE) {
                    fprintf(stderr, "Bad L operand / imm too large: %s\n", line);
                    return 0;
                }
                write_instr(output, desc->opcode, 0, 0, 0, (uint32_t)imm);
            }
            else if (desc->fmt == FMT_RRL) {
                uint8_t rd, rs;
                uint64_t imm;
                if (!t1 || !t2 || !t3 || t4) {
                    fprintf(stderr, "Bad RRL format: %s\n", line);
                    free(t1); free(t2); free(t3); free(t4); free(op);
                    return 0;
                }
                if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs)
                    || !parse_u64_literal(t3, &imm) || imm > MAX_IMMEDIATE_SIZE) {
                    fprintf(stderr, "Bad RRL operands / imm too large: %s\n", line);
                    return 0;
                }
                write_instr(output, desc->opcode, rd, rs, 0, (uint32_t)imm);
            }
            else if (desc->fmt == FMT_PRIV) {
                uint8_t rd, rs, rt;
                uint64_t imm;
                if (!t1 || !t2 || !t3 || !t4 || t5) {
                    fprintf(stderr, "Bad PRIV format: %s\n", line);
                    free(t1); free(t2); free(t3); free(t4); free(op);
                    return 0;
                }
                if (!parse_reg_num(t1, &rd) || !parse_reg_num(t2, &rs) || !parse_reg_num(t3, &rt)
                    || !parse_u64_literal(t4, &imm) || imm > MAX_IMMEDIATE_SIZE) {
                    fprintf(stderr, "Bad PRIV operands: %s\n", line);
                    return 0;
                }
                write_instr(output, desc->opcode, rd, rs, rt, (uint32_t)imm);
            } 
            else if (desc->fmt == FMT_NONE) {
                if (t1) {
                    fprintf(stderr, "Unexpected operand for no-operand instruction: %s\n", line);
                    free(t1); free(t2); free(t3); free(t4); free(op);
                    return 0;
                }
                write_instr(output, desc->opcode, 0, 0, 0, 0);
            }
            else {
                fprintf(stderr, "Unhandled format in Stage 2: %s\n", op);
                return 0;
            }

            free(op);
            free(t1); free(t2); free(t3); free(t4);
        }
        else if (section == 1) {
            char *tok = parse_token(&p);
            uint64_t v;
            if (!tok || !parse_u64_literal(tok, &v)) {
                fprintf(stderr, "Bad data literal: %s\n", line);
                return 0;
            }
            write_u64(output, v);
            free(tok);
        }
        else {
            fprintf(stderr, "Content outside section: %s\n", line);
            return 0;
        }
    } return 1;
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