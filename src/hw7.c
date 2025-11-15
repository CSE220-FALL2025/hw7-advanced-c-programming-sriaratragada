#include "hw7.h"

#include <ctype.h>
#include <errno.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static inline void *xmalloc(size_t n) {
    void *p = malloc(n);
    if (!p) { fprintf(stderr, "Out of memory\n"); exit(1); }
    return p;
}

static inline char *xstrdup(const char *s) {
    size_t n = strlen(s) + 1;
    char *p = (char *)xmalloc(n);
    memcpy(p, s, n);
    return p;
}

static inline int is_alpha_matrix_name(char c) {
    return isalpha((unsigned char)c);
}

static inline char *ltrim(char *s) {
    while (*s && isspace((unsigned char)*s)) ++s;
    return s;
}
static inline void rtrim_inplace(char *s) {
    size_t n = strlen(s);
    while (n && isspace((unsigned char)s[n-1])) { s[--n] = '\0'; }
}
static inline char *trim(char *s) {
    s = ltrim(s);
    rtrim_inplace(s);
    return s;
}

matrix_sf* add_mats_sf(const matrix_sf *a, const matrix_sf *b) {
    assert(a && b);
    assert(a->num_rows == b->num_rows && a->num_cols == b->num_cols);
    unsigned int r = a->num_rows, c = a->num_cols;
    matrix_sf *m = (matrix_sf*)xmalloc(sizeof(matrix_sf) + r*c*sizeof(int));
    m->name = '?'; m->num_rows = r; m->num_cols = c;
    for (unsigned int i = 0; i < r*c; ++i) m->values[i] = a->values[i] + b->values[i];
    return m;
}

matrix_sf* mult_mats_sf(const matrix_sf *a, const matrix_sf *b) {
    assert(a && b);
    assert(a->num_cols == b->num_rows);
    unsigned int r = a->num_rows, mid = a->num_cols, c = b->num_cols;
    matrix_sf *m = (matrix_sf*)xmalloc(sizeof(matrix_sf) + r*c*sizeof(int));
    m->name = '?'; m->num_rows = r; m->num_cols = c;
    for (unsigned int i = 0; i < r; ++i) {
        for (unsigned int j = 0; j < c; ++j) {
            long long acc = 0;
            for (unsigned int k = 0; k < mid; ++k) {
                acc += (long long)a->values[i*mid + k] * (long long)b->values[k*c + j];
            }
            m->values[i*c + j] = (int)acc;
        }
    }
    return m;
}

matrix_sf* transpose_mat_sf(const matrix_sf *a) {
    assert(a);
    unsigned int r = a->num_rows, c = a->num_cols;
    matrix_sf *m = (matrix_sf*)xmalloc(sizeof(matrix_sf) + r*c*sizeof(int));
    m->name = '?'; m->num_rows = c; m->num_cols = r;
    for (unsigned int i = 0; i < r; ++i) {
        for (unsigned int j = 0; j < c; ++j) {
            m->values[j*r + i] = a->values[i*c + j];
        }
    }
    return m;
}

bst_sf* insert_bst_sf(matrix_sf *mat, bst_sf *root) {
    if (!root) {
        bst_sf *node = (bst_sf*)xmalloc(sizeof(bst_sf));
        node->mat = mat; node->left_child = node->right_child = NULL;
        return node;
    }
    bst_sf *cur = root;
    while (1) {
        if (mat->name < cur->mat->name) {
            if (cur->left_child) cur = cur->left_child;
            else {
                bst_sf *node = (bst_sf*)xmalloc(sizeof(bst_sf));
                node->mat = mat; node->left_child = node->right_child = NULL;
                cur->left_child = node; break;
            }
        } else {
            if (cur->right_child) cur = cur->right_child;
            else {
                bst_sf *node = (bst_sf*)xmalloc(sizeof(bst_sf));
                node->mat = mat; node->left_child = node->right_child = NULL;
                cur->right_child = node; break;
            }
        }
    }
    return root;
}

matrix_sf* find_bst_sf(char name, bst_sf *root) {
    bst_sf *cur = root;
    while (cur) {
        if (name == cur->mat->name) return cur->mat;
        cur = (name < cur->mat->name) ? cur->left_child : cur->right_child;
    }
    return NULL;
}

void free_bst_sf(bst_sf *root) {
    if (!root) return;
    free_bst_sf(root->left_child);
    free_bst_sf(root->right_child);
    if (root->mat) free(root->mat);
    free(root);
}

static inline void skip_spaces(const char **p) { while (**p && isspace((unsigned char)**p)) (*p)++; }

static int read_int_token(const char **p, int *out) {
    skip_spaces(p);
    errno = 0;
    char *endptr;
    long v = strtol(*p, &endptr, 10);
    if (endptr == *p) return 0;
    if (errno == ERANGE) return 0;
    *out = (int)v;
    *p = endptr;
    return 1;
}

matrix_sf* create_matrix_sf(char name, const char *expr) {
    const char *p = expr;
    int nr, nc;
    int ok = read_int_token(&p, &nr); assert(ok && nr > 0);
    ok = read_int_token(&p, &nc); assert(ok && nc > 0);
    skip_spaces(&p);
    while (*p && *p != '[') ++p;
    assert(*p == '[');
    ++p;
    matrix_sf *m = (matrix_sf*)xmalloc(sizeof(matrix_sf) + (size_t)nr*(size_t)nc*sizeof(int));
    m->name = name; m->num_rows = (unsigned)nr; m->num_cols = (unsigned)nc;
    for (int r = 0; r < nr; ++r) {
        for (int c = 0; c < nc; ++c) {
            int val, got = read_int_token(&p, &val);
            assert(got);
            m->values[r*nc + c] = val;
        }
        skip_spaces(&p);
        assert(*p == ';'); ++p;
    }
    skip_spaces(&p);
    assert(*p == ']');
    return m;
}

static int precedence(char op) {
    switch (op) {
        case '\'': return 3;
        case '*':  return 2;
        case '+':  return 1;
        default:   return 0;
    }
}
static int is_operator(char ch) {
    return (ch == '+' || ch == '*' || ch == '\'' || ch == '(' || ch == ')');
}

char* infix2postfix_sf(char *infix) {
    size_t n = strlen(infix);
    char *out = (char*)xmalloc(n + 8);
    size_t out_len = 0;
    char *stack = (char*)xmalloc(n + 8);
    int top = -1;
    for (size_t i = 0; i < n; ++i) {
        char ch = infix[i];
        if (isspace((unsigned char)ch)) continue;
        if (isalpha((unsigned char)ch)) {
            out[out_len++] = ch;
        } else if (ch == '\'') {
            out[out_len++] = '\'';
        } else if (ch == '(') {
            stack[++top] = ch;
        } else if (ch == ')') {
            while (top >= 0 && stack[top] != '(') {
                out[out_len++] = stack[top--];
            }
            if (top >= 0 && stack[top] == '(') --top;
        } else if (ch == '+' || ch == '*') {
            int p = precedence(ch);
            while (top >= 0 && stack[top] != '(' && precedence(stack[top]) >= p) {
                out[out_len++] = stack[top--];
            }
            stack[++top] = ch;
        }
    }
    while (top >= 0) out[out_len++] = stack[top--];
    out[out_len] = '\0';
    free(stack);
    return out;
}

typedef struct {
    matrix_sf **data;
    int top;
    int cap;
} MatStack;

static void mstack_init(MatStack *s, int cap) {
    s->data = (matrix_sf**)xmalloc(sizeof(matrix_sf*) * (size_t)cap);
    s->top = -1; s->cap = cap;
}
static void mstack_free(MatStack *s) {
    free(s->data);
    s->data = NULL; s->top = -1; s->cap = 0;
}
static void mstack_push(MatStack *s, matrix_sf *m) {
    if (s->top+1 >= s->cap) {
        s->cap = s->cap*2 + 8;
        s->data = (matrix_sf**)realloc(s->data, sizeof(matrix_sf*)*(size_t)s->cap);
        if (!s->data) { fprintf(stderr, "Out of memory\n"); exit(1); }
    }
    s->data[++s->top] = m;
}
static matrix_sf* mstack_pop(MatStack *s) {
    assert(s->top >= 0);
    return s->data[s->top--];
}

static int is_temp(const matrix_sf *m) {
    return !is_alpha_matrix_name(m->name);
}

matrix_sf* evaluate_expr_sf(char name, char *expr, bst_sf *root) {
    char *post = infix2postfix_sf(expr);
    MatStack st; mstack_init(&st, 8);
    for (size_t i = 0; post[i]; ++i) {
        char ch = post[i];
        if (isspace((unsigned char)ch)) continue;
        if (isalpha((unsigned char)ch)) {
            matrix_sf *ref = find_bst_sf(ch, root);
            assert(ref != NULL);
            mstack_push(&st, ref);
        } else if (ch == '\'') {
            matrix_sf *a = mstack_pop(&st);
            matrix_sf *t = transpose_mat_sf(a);
            t->name = 1;
            mstack_push(&st, t);
            if (is_temp(a)) { free(a); }
        } else if (ch == '+' || ch == '*') {
            matrix_sf *b = mstack_pop(&st);
            matrix_sf *a = mstack_pop(&st);
            matrix_sf *t = (ch == '+') ? add_mats_sf(a, b) : mult_mats_sf(a, b);
            t->name = 1;
            mstack_push(&st, t);
            if (is_temp(a)) free(a);
            if (is_temp(b)) free(b);
        }
    }
    matrix_sf *res = mstack_pop(&st);
    assert(st.top == -1);
    mstack_free(&st);
    free(post);
    res->name = name;
    return res;
}

static int line_is_empty(const char *s) {
    while (*s) { if (!isspace((unsigned char)*s)) return 0; ++s; }
    return 1;
}

static void split_lhs_rhs(char *line, char *out_lhs_name, char **out_rhs) {
    char *eq = strchr(line, '=');
    assert(eq != NULL);
    char *p = eq;
    while (p > line && isspace((unsigned char)p[-1])) --p;
    --p;
    assert(isalpha((unsigned char)*p));
    *out_lhs_name = *p;
    char *rhs = eq + 1;
    rhs = trim(rhs);
    *out_rhs = rhs;
}

matrix_sf *execute_script_sf(char *filename) {
    FILE *fp = fopen(filename, "r");
    assert(fp != NULL);
    bst_sf *root = NULL;
    matrix_sf *last = NULL;
    char *buf = NULL;
    size_t cap = MAX_LINE_LEN;
    ssize_t got;
    while ((got = getline(&buf, &cap, fp)) != -1) {
        buf[got] = '\0';
        char *line = trim(buf);
        if (line_is_empty(line)) continue;
        char name; char *rhs;
        split_lhs_rhs(line, &name, &rhs);
        int is_def = 0;
        for (char *q = rhs; *q; ++q) {
            if (*q == '[') { is_def = 1; break; }
        }
        matrix_sf *m = NULL;
        if (is_def) {
            m = create_matrix_sf(name, rhs);
        } else {
            m = evaluate_expr_sf(name, rhs, root);
        }
        root = insert_bst_sf(m, root);
        last = m;
    }
    if (buf) free(buf);
    fclose(fp);
    return last;
}

matrix_sf *copy_matrix(unsigned int num_rows, unsigned int num_cols, int values[]) {
    matrix_sf *m = malloc(sizeof(matrix_sf)+num_rows*num_cols*sizeof(int));
    m->name = '?';
    m->num_rows = num_rows;
    m->num_cols = num_cols;
    memcpy(m->values, values, num_rows*num_cols*sizeof(int));
    return m;
}

void print_matrix_sf(matrix_sf *mat) {
    assert(mat != NULL);
    assert(mat->num_rows <= 1000);
    assert(mat->num_cols <= 1000);
    printf("%d %d ", mat->num_rows, mat->num_cols);
    for (unsigned int i = 0; i < mat->num_rows*mat->num_cols; i++) {
        printf("%d", mat->values[i]);
        if (i < mat->num_rows*mat->num_cols-1)
            printf(" ");
    }
    printf("\n");
}
