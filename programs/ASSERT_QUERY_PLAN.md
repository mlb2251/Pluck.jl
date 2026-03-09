# Assert-Query Conversion Plan

## Overview

Convert all Marginal and Posterior queries in `programs/*.pluck` (not subfolders, not PosteriorSamples) to `assert-query` statements. The assert-query syntax is:

```scheme
(assert-query
 'query-name
 <query-expression>
 (value1 probability1)
 (value2 probability2)
 ...)
```

All value types (bracket lists, strings, bare numbers, paren ADT values) are supported by the parser. List ALL result values for each query, not just a subset. Run `julia --project -e 'using Pluck; load_pluck_file("programs/<file>.pluck")'` after converting each file to verify PASS.

## Already Done (skip these)

| File | Query | Status |
|------|-------|--------|
| fig1.pluck | `lazy-to-lucky` | Already assert-query |
| fig1.pluck | `goat-or-bat` | Already assert-query |
| fig1-strings.pluck | `goat-or-bat` | Already assert-query |

## Queries to Convert

### 1. simple_example.pluck

**num-greater-than-five** (Marginal)
```
((False) 0.7064862000000001)
((True) 0.2935138000000001)
```

**posterior-given-less-than-five** (Posterior)
```
(1 0.24317453299436276)
(0 0.22106775726760244)
(2 0.21443572454957446)
(3 0.17751740908588484)
(4 0.14380457610257547)
```

### 2. fig1-strings.pluck

**lazy-to-lucky** (Marginal)
```
((False) 0.9999999999967386)
((True) 3.2614371064714946e-12)
```

### 3. fig2.pluck

**first-two-elements-are-zero** (Marginal)
```
((False) 0.9375)
((True) 0.0625)
```

**second-element-given-first-and-third** (Posterior)
```
(2 0.25)
(3 0.25)
(4 0.25)
(5 0.25)
```

### 4. burglary.pluck

**burglary-given-that-mary-called** (Posterior)
```
((False) 0.9970065507586944)
((True) 0.0029934492413055437)
```

### 5. diamond.pluck

**network-100** (Marginal)
```
((True) 0.9950123548119845)
((False) 0.004987645188015855)
```

### 6. hmm.pluck

**posterior-first-fifty-latents** (Posterior)
```
((True) 0.6338219329206617)
((False) 0.36617806707933825)
```

### 7. pcfg.pluck

**probability-of-string** (Marginal)
```
((False) 0.9999999602635702)
((True) 3.973642985224724e-8)
```

**posterior-on-strings** (Posterior)
```
([(a_), (c_), (a_)] 0.250000000003125)
([(c_), (a_), (a_)] 0.250000000003125)
([(b_), (a_), (a_), (c_)] 0.1250000000015625)
([(c_), (b_), (a_), (a_)] 0.1250000000015625)
([(b_), (a_), (a_), (c_), (a_)] 0.06250000000078125)
([(c_), (b_), (a_), (a_), (a_)] 0.06250000000078125)
([(a_), (c_), (a_), (c_)] 0.04166666666302083)
([(c_), (c_), (a_), (a_)] 0.04166666666302083)
([(a_), (c_), (a_), (c_), (a_)] 0.020833333331510415)
([(c_), (c_), (a_), (a_), (a_)] 0.020833333331510415)
```

**probability-of-sentence** (Marginal)
```
((False) 0.9952361111113492)
((True) 0.004763888888650694)
```

**short-sentence** (Posterior)
```
([(a_), (cat_), (barks_)] 0.08333333333750001)
([(a_), (cat_), (eats_)] 0.08333333333750001)
([(a_), (dog_), (barks_)] 0.08333333333750001)
([(a_), (dog_), (eats_)] 0.08333333333750001)
([(the_), (cat_), (barks_)] 0.08333333333750001)
([(the_), (cat_), (eats_)] 0.08333333333750001)
([(the_), (dog_), (barks_)] 0.08333333333750001)
([(the_), (dog_), (eats_)] 0.08333333333750001)
([(a_), (bone_), (barks_)] 0.08333333332500001)
([(a_), (bone_), (eats_)] 0.08333333332500001)
([(the_), (bone_), (barks_)] 0.08333333332500001)
([(the_), (bone_), (eats_)] 0.08333333332500001)
```

**infilling-given-fifth-word-tasty** (Posterior) — very large output, include ALL values. Run the query to get the full list: `julia --project -e 'using Pluck; load_pluck_file("programs/pcfg.pluck")'` and capture the infilling output. Every printed `value  probability` line becomes `(value probability)` in the assert-query.

### 8. regex.pluck

**short** (Posterior)
```
("abc" 0.5333333333333333)
("ababc" 0.26666666666666666)
("abababc" 0.13333333333333333)
("ababababc" 0.06666666666666667)
```

**parse** (Posterior)
```
((Concat (KleeneStar (String "ab")) (String "c")) 0.6575342465866016)
((Concat (KleeneStar (Concat (String "a") (String "b"))) (String "c")) 0.3424657534133984)
```

**together** (Posterior)
```
("abc" 0.5333333333333333)
("ababc" 0.26666666666666666)
("abababc" 0.13333333333333333)
("ababababc" 0.06666666666666667)
```

**infer-re** (Posterior) — very large output, include ALL values. Run the query and capture the full infer-re output.

**which-regex** (Posterior)
```
((KleeneStar (Sum (String "a") (String "b"))) 0.8241758241903152)
((Sum (KleeneStar (String "a")) (KleeneStar (String "b"))) 0.1758241758096848)
```

### 9. strings.pluck

**uncertain-world** (Posterior)
```
(["Hello uncertain", "world!"] 0.5000000000000001)
(["Hello", "uncertain world!"] 0.49999999999999994)
```

**namelist** (Posterior)
```
(["Emily Jane McClellan"] 0.9365920405321279)
(["Emily", "Jane McClellan"] 0.05853700253325799)
(["Emily Jane Mc", "Clellan"] 0.004584430056107424)
(["Emily", "Jane Mc", "Clellan"] 0.000286526878506714)
```

### 10. talk_examples.pluck (7 unnamed queries — need names added)

These queries currently have no name (just `(query (Marginal ...))`). Change to `(assert-query 'name ...)` with a quoted name.

**talk-hypothesis-1** (Marginal)
```
((False) 1.0)
((True) 1.3552527156068805e-20)
```

**talk-hypothesis-2** (Marginal)
```
((False) 1.0)
((True) 2.7755575615628914e-17)
```

**talk-hypothesis-3** (Marginal)
```
((False) 0.9999999994534107)
((True) 5.465893523925493e-10)
```

**talk-hypothesis-4** (Marginal)
```
((False) 0.998046875)
((True) 0.001953125)
```

**talk-hypothesis-5** (Marginal)
```
((True) 1.0)
```

**talk-hypothesis-alt-1** (Marginal)
```
((False) 1.0)
```

**talk-hypothesis-alt-2** (Marginal)
```
((False) 1.0)
((True) 5.421010862427522e-20)
```

### 11. types.pluck (4 unnamed queries — need names added)

These queries currently have no name. Change to `(assert-query 'name ...)` with a quoted name.

**my-add-4-5** (Marginal)
```
(9 1.0)
```

**my-map-double** (Marginal)
```
([2, 4, 6, 8, 10] 1.0)
```

**rand-mytype-eq** (Marginal)
```
((False) 0.875)
((True) 0.125)
```

**type-inference** (Marginal)
```
((Some [(MyNat)]) 0.375)
```
