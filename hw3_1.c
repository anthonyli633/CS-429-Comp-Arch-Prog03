// tinker_stage1.c
// Stage 1: read .tk, expand macros to an intermediate .tk (no macros), with labels resolved.
// Two-pass: Pass 1 builds a label->address table using EXPANDED sizes; Pass 2 writes expanded code.
//
// Assumptions (common in Stage 1):
// - Address space starts at 0x1000.
// - Each real instruction is 4 bytes.
// - Each .data item is a 64-bit value => 8 bytes.
// - Code + data are laid out in the same address space in source order (directives switch interpretation).

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdint.h>
#include <stdbool.h>
#include <errno.h>

#define MAX_LABELS 4096
#define MAX_LINE   1024

typedef struct {
    char name[64];
    uint64_t addr;
} Label;

static Label labels[MAX_LABELS];
static int label_count = 0;

static void die(const char *msg, const char *line) {
    if (line) fprintf(stderr, "%s: %s\n", msg, line);
    else fprintf(stderr, "%s\n", msg);
    exit(1);
}

static void rstrip(char *s) {
    size_t n = strlen(s);
    while (n > 0 && isspace((unsigned char)s[n - 1])) s[--n] = '\0';
}

static char *my_strdup(const char *s) {
    size_t len = strlen(s) + 1;
    char *p = (char*)malloc(len);
    if (!p) return NULL;
    memcpy(p, s, len);
    return p;
}

// Returns malloc'd token or NULL if none.
// Delimiters: whitespace and ','.
static char* parse_token(char **p) {
    if (!p || !*p) return NULL;

    while (**p && (isspace((unsigned char)**p) || **p == ',')) (*p)++;
    if (**p == '\0') return NULL;

    char token[128];
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
    errno = 0;
    char *end = NULL;
    unsigned long long v = strtoull(s, &end, 0); // supports 0x...
    if (errno != 0 || end == s || *end != '\0') return false;
    *out = (uint64_t)v;
    return true;
}

static void add_label(const char *name, uint64_t addr) {
    if (label_count >= MAX_LABELS) die("Too many labels", NULL);

    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, name) == 0) {
            fprintf(stderr, "Duplicate label: %s\n", name);
            exit(1);
        }
    }

    strncpy(labels[label_count].name, name, sizeof(labels[label_count].name) - 1);
    labels[label_count].name[sizeof(labels[label_count].name) - 1] = '\0';
    labels[label_count].addr = addr;
    label_count++;
}

static bool lookup_label(const char *name, uint64_t *out) {
    for (int i = 0; i < label_count; i++) {
        if (strcmp(labels[i].name, name) == 0) {
            *out = labels[i].addr;
            return true;
        }
    }
    return false;
}

// Emit the canonical ld expansion you requested (12-bit chunks + final 4-bit nibble).
// Emits 11 real instructions total:
// xor + (addi,shftli)*5 + addi
static void emit_ld(FILE *intermediate, const char *rd, uint64_t L) {
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

typedef enum { SEC_NONE=-1, SEC_CODE=0, SEC_DATA=1 } Section;

static void skip_leading_ws(char **p) {
    while (**p && isspace((unsigned char)**p)) (*p)++;
}

// PASS 1: compute label addresses with macro expansion sizes
static void pass1_build_labels(FILE *input) {
    char line[MAX_LINE];
    Section sec = SEC_NONE;
    uint64_t loc = 0x1000;

    while (fgets(line, sizeof(line), input)) {
        char *p = line;
        skip_leading_ws(&p);
        if (*p == '\0' || *p == '\n') continue;

        if (*p == ';') continue;

        if (*p == '.') {
            if (strncmp(p, ".code", 5) == 0) sec = SEC_CODE;
            else if (strncmp(p, ".data", 5) == 0) sec = SEC_DATA;
            else die("Unknown directive", line);
            continue;
        }

        if (*p == ':') {
            // label name is after ':'
            char name[64];
            strncpy(name, p + 1, sizeof(name) - 1);
            name[sizeof(name) - 1] = '\0';
            rstrip(name);
            add_label(name, loc);
            continue;
        }

        // instruction/data lines must begin with a tab in the spec, but we accept any leading ws.
        if (sec == SEC_NONE) die("Line outside of .code/.data", line);

        if (sec == SEC_DATA) {
            // a single 64-bit item
            loc += 8;
        } else {
            // code: count emitted real instructions for this source line
            // parse opcode
            char op[16];
            int oi = 0;
            while (*p && !isspace((unsigned char)*p) && oi < (int)sizeof(op)-1) op[oi++] = *p++;
            op[oi] = '\0';

            int emitted = 1; // default: real instruction already

            if (strcmp(op, "clr") == 0) emitted = 1;
            else if (strcmp(op, "in") == 0) emitted = 1;   // priv ...
            else if (strcmp(op, "out") == 0) emitted = 1;  // priv ...
            else if (strcmp(op, "push") == 0) emitted = 2; // subi + mov(store)
            else if (strcmp(op, "pop") == 0) emitted = 2;  // mov(load) + addi
            else if (strcmp(op, "halt") == 0) emitted = 1; // priv ...,0
            else if (strcmp(op, "ld") == 0) emitted = 11;  // xor + add/shift chain

            loc += 4ULL * (uint64_t)emitted;
        }
    }
}

// PASS 2: write intermediate expanded code with labels resolved for ld
static void pass2_write_intermediate(FILE *input, FILE *intermediate) {
    char line[MAX_LINE];
    Section sec = SEC_NONE;

    while (fgets(line, sizeof(line), input)) {
        char *p = line;
        skip_leading_ws(&p);
        if (*p == '\0' || *p == '\n') continue;

        if (*p == ';') continue;

        if (*p == '.') {
            if (strncmp(p, ".code", 5) == 0) {
                if (sec != SEC_CODE) fprintf(intermediate, ".code\n");
                sec = SEC_CODE;
            } else if (strncmp(p, ".data", 5) == 0) {
                if (sec != SEC_DATA) fprintf(intermediate, ".data\n");
                sec = SEC_DATA;
            } else die("Unknown directive", line);
            continue;
        }

        if (*p == ':') {
            // preserve labels in intermediate
            // strip trailing spaces/newline and print as ":NAME\n"
            char tmp[MAX_LINE];
            strncpy(tmp, p, sizeof(tmp)-1);
            tmp[sizeof(tmp)-1] = '\0';
            rstrip(tmp);
            fprintf(intermediate, "%s\n", tmp);
            continue;
        }

        if (sec == SEC_NONE) die("Line outside of .code/.data", line);

        if (sec == SEC_DATA) {
            // Keep data as text in intermediate (stage 1 goal is intermediate asm)
            // Normalize to "\t<literal>\n"
            char *tok = parse_token(&p);
            if (!tok) die("Malformed data item", line);
            fprintf(intermediate, "\t%s\n", tok);
            free(tok);
            continue;
        }

        // CODE: parse opcode then expand macros
        char op[16];
        int oi = 0;
        while (*p && !isspace((unsigned char)*p) && oi < (int)sizeof(op)-1) op[oi++] = *p++;
        op[oi] = '\0';

        // move p past spaces before operands
        while (*p && isspace((unsigned char)*p)) p++;

        if (strcmp(op, "clr") == 0) {
            char *rd = parse_token(&p);
            if (!rd) die("Malformed clr", line);
            fprintf(intermediate, "\txor %s, %s, %s\n", rd, rd, rd);
            free(rd);

        } else if (strcmp(op, "in") == 0) {
            char *rd = parse_token(&p);
            char *rs = parse_token(&p);
            if (!rd || !rs) die("Malformed in rd, rs", line);
            fprintf(intermediate, "\tpriv %s, %s, r0, 3\n", rd, rs);
            free(rd); free(rs);

        } else if (strcmp(op, "out") == 0) {
            // Support both: out rd, rs   AND   out rs (shorthand)
            char *a = parse_token(&p);
            char *b = parse_token(&p);

            if (!a) die("Malformed out", line);

            if (b) {
                // out rd, rs
                fprintf(intermediate, "\tpriv %s, %s, r0, 4\n", a, b);
            } else {
                // out rs  (default port in r0)
                fprintf(intermediate, "\tpriv r0, %s, r0, 4\n", a);
            }

            free(a);
            free(b);

        } else if (strcmp(op, "push") == 0) {
            char *rd = parse_token(&p);
            if (!rd) die("Malformed push", line);
            fprintf(intermediate, "\tsubi r31, 8\n");
            fprintf(intermediate, "\tmov (r31)(0), %s\n", rd);
            free(rd);

        } else if (strcmp(op, "pop") == 0) {
            char *rd = parse_token(&p);
            if (!rd) die("Malformed pop", line);
            fprintf(intermediate, "\tmov %s, (r31)(0)\n", rd);
            fprintf(intermediate, "\taddi r31, 8\n");
            free(rd);

        } else if (strcmp(op, "halt") == 0) {
            fprintf(intermediate, "\tpriv r0, r0, r0, 0\n");

        } else if (strcmp(op, "ld") == 0) {
            char *rd = parse_token(&p);
            char *L  = parse_token(&p);
            if (!rd || !L) die("Malformed ld rd, L", line);

            uint64_t val;
            if (L[0] == ':') {
                if (!lookup_label(L + 1, &val)) {
                    fprintf(stderr, "Unknown label in ld: %s\n", L);
                    exit(1);
                }
            } else {
                if (!parse_u64_literal(L, &val)) die("Invalid literal in ld", line);
            }

            emit_ld(intermediate, rd, val);

            free(rd);
            free(L);

        } else {
            // Not a macro: just pass the instruction through, normalized with a tab
            // Print from the trimmed pointer p? Easiest: print original line but ensure it starts with tab.
            // We'll print the trimmed version with a tab and newline.
            char tmp[MAX_LINE];
            strncpy(tmp, p - (int)strlen(op), sizeof(tmp)-1); // include opcode onwards
            tmp[sizeof(tmp)-1] = '\0';
            rstrip(tmp);
            fprintf(intermediate, "\t%s\n", tmp);
        }
    }
}

int main(int argc, char *argv[]) {
    if (argc != 3) {
        fprintf(stderr, "Usage: %s input.tk intermediate.tk\n", argv[0]);
        return 1;
    }

    FILE *input = fopen(argv[1], "r");
    if (!input) { perror("open input"); return 1; }

    // Pass 1: labels
    pass1_build_labels(input);

    // Pass 2: emit intermediate
    rewind(input);

    FILE *intermediate = fopen(argv[2], "w");
    if (!intermediate) { perror("open intermediate"); fclose(input); return 1; }

    pass2_write_intermediate(input, intermediate);

    fclose(input);
    fclose(intermediate);
    return 0;
}
