#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>

#define MAX_LABELS 1024

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
    FMT_PRIV   // rd, rs, rt, L
} InstrFormat;

typedef struct {
    const char *name;
    InstrFormat fmt;
    Opcode opcode;
} InstrDesc;

static const InstrDesc instr_table[] = {
    { "add",    FMT_RRR, OP_ADD    },
    { "addi",   FMT_RI,  OP_ADDI   },
    { "sub",    FMT_RRR, OP_SUB    },
    { "subi",   FMT_RI,  OP_SUBI   },
    { "xor",    FMT_RRR, OP_XOR    },
    { "shftli", FMT_RI,  OP_SHFTLI },
    { "br",     FMT_R,   OP_BR     },
    { "priv",   FMT_PRIV,OP_PRIV  },
    { "mov",    FMT_RR,  OP_MOV_RR },
    { "mov",    FMT_RI,  OP_MOV_RL },
    { "mov",    FMT_RRL, OP_MOV_MR },
    { "mov",    FMT_RRL, OP_MOV_RM },
    { "halt",   FMT_PRIV,OP_PRIV  }, // priv with L=0
    { NULL,     0,       0         }
};


// Labels
typedef struct {
    char name[64];
    uint64_t addr;
} Label;

static Label labels[MAX_LABELS];
static int label_count = 0;

void add_label(const char *name, uint64_t addr) {
    strncpy(labels[label_count].name, name, 63);
    labels[label_count].name[63] = '\0';
    labels[label_count].addr = addr;
    label_count++;
}
uint64_t get_addr(const char *label) {
    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, label) == 0) {
            return labels[i].addr;
        }
    } return -1;
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

    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 0); // base 0 supports 0x...
    if (errno != 0 || end == s || *end != '\0') return false;
    *out = (uint64_t)v;
    return true;
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
            rstrip(p + 1);
            add_label(p + 1, pc);
        } else if (*p == '.') {
            if (strncmp(p, ".code", 5) == 0) { type = 0; }
            else if (strncmp(p, ".data", 5) == 0) { type = 1; }
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
                char* token = NULL;
                fprintf(intermediate, "\t%s", instr);
                do {
                    token = parse_token(&p);
                    if (token) {
                        fprintf(intermediate, " %s", token);
                        free(token);
                    } else break;
                } while (true);
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
    fclose(output);
    return 0;
}