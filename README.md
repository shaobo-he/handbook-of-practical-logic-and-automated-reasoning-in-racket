# Racket Implementation of John Harrison's *Handbook of Practical Logic and Automated Reasoning*

[![CI](https://github.com/shaobo-he/handbook-of-practical-logic-and-automated-reasoning-in-racket/actions/workflows/ci.yml/badge.svg)](https://github.com/shaobo-he/handbook-of-practical-logic-and-automated-reasoning-in-racket/actions/workflows/ci.yml)

A port of the book's code (<https://www.cl.cam.ac.uk/~jrh13/atp/>), following the
book's module structure. Everything is plain (untyped) `racket/base`; formulas
and terms are represented directly as s-expressions, so Racket's reader doubles as
the parser.

## Representation

```
term    ::= (var x) | (fn f t ...)
atom    ::= (rel R t ...)
formula ::= #t | #f | (atom a)
          | (not p) | (and p q) | (or p q) | (imp p q) | (iff p q)
          | (forall x p) | (exists x p)
```

## Layout

```
core/        lib formulas intro
prop/        prop propexamples defcnf dp stal bdd
fol/         fol skolem herbrand unif tableaux resolution prolog meson skolems
equality/    equal cong rewrite order completion eqelim paramodulation
decidable/   decidable qelim cooper complex real grobner geom interpolation combining
lcf/         lcf lcfprop folderived lcffol tactics limitations
tests/       <name>-test.rkt unit suites; property/ holds the rackcheck suite
```

Modules in the same directory `require` each other by bare name; cross-directory
requires use `../dir/name.rkt`.

## Modules (vs. the book)

The `File` column gives the path under the directory shown in the layout above.

| File          | Book module     | Status |
|---------------|-----------------|--------|
| `lib.rkt`     | `lib`           | sets, finite partial functions, union-find (hash-based) |
| `intro.rkt`   | `intro`         | toy algebra: datatype, simplifier, lexer/parser/printer |
| `formulas.rkt`| `formulas`      | atom traversal, conjuncts/disjuncts, printer |
| `prop.rkt`    | `prop`          | eval, truth tables, tautology, simplify, NNF/NENF, DNF/CNF |
| `propexamples.rkt`| `propexamples` | Ramsey, adders, multiplier, primality formulas |
| `defcnf.rkt`  | `defcnf`        | definitional (Tseitin) CNF, incl. 3-CNF variant |
| `dp.rkt`      | `dp`            | DP, DPLL, iterative DPLL (backtracking + backjumping/learning) |
| `stal.rkt`    | `stal`          | Stalmarck's method |
| `bdd.rkt`     | `bdd`           | binary decision diagrams; tautology checking (plain + shared defs) |
| `fol.rkt`     | `fol`           | semantics, free vars, substitution, function symbols |
| `skolem.rkt`  | `skolem`        | simplify, NNF, prenex, Skolemization |
| `unif.rkt`    | `unif`          | first-order unification |
| `herbrand.rkt`| `herbrand`      | Gilmore + first-order Davis-Putnam (with refinement) |
| `tableaux.rkt`| `tableaux`      | Prawitz + analytic tableaux (iterative deepening), `splittab` |
| `resolution.rkt`| `resolution`  | resolution: basic, subsumption/deletion, positive, set-of-support |
| `prolog.rkt`  | `prolog`        | Horn backchaining + toy Prolog (over s-expr rules) |
| `meson.rkt`   | `meson`         | MESON model elimination (basic + divide-and-conquer) |
| `skolems.rkt` | `skolems`       | Skolemizing a set of formulas at once |
| `equal.rkt`   | `equal`         | equality axioms + `equalitize` |
| `cong.rkt`    | `cong`          | congruence closure (decision procedure for ground equality) |
| `rewrite.rkt` | `rewrite`       | term rewriting to normal form |
| `order.rkt`   | `order`         | term size + lexicographic path order (LPO) |
| `completion.rkt`| `completion`  | Knuth-Bendix completion + interreduction |
| `eqelim.rkt`  | `eqelim`        | Brand transformation; `bmeson`, `emeson` |
| `paramodulation.rkt`| `paramodulation` | paramodulation in the resolution loop |
| `decidable.rkt`| `decidable`    | AE fragment, finite-model methods, monadic fragment |
| `qelim.rkt`   | `qelim`         | QE framework + dense linear orders |
| `cooper.rkt`  | `cooper`        | Presburger arithmetic (Cooper's algorithm) |
| `complex.rkt` | `complex`       | QE for algebraically closed fields |
| `real.rkt`    | `real`          | QE for real-closed fields (Cohen-Hormander) |
| `grobner.rkt` | `grobner`       | Grobner bases + `grobner-decide` |
| `geom.rkt`    | `geom`          | geometry via coordinates + Wu's method |
| `interpolation.rkt`| `interpolation` | Craig-Robinson interpolation |
| `combining.rkt`| `combining`    | Nelson-Oppen combined decision procedure |
| `lcf.rkt`     | `lcf`           | LCF kernel: primitive rules + axiom schemes |
| `lcfprop.rkt` | `lcfprop`       | derived propositional rules; `lcftaut` |
| `folderived.rkt`| `folderived`  | derived first-order rules (`isubst`, `ispec`, ...) |
| `lcffol.rkt`  | `lcffol`        | LCF first-order prover (proof-producing tableaux) |
| `tactics.rkt` | `tactics`       | goal/tactic system + declarative proof layer |
| `limitations.rkt`| `limitations` | Goedel numbering, Δ-decider, Σ/Π/Δ, Turing machines, Robinson eval |

Substitutions / finite partial functions are immutable hashes from variable
name to term.

Unit tests live in `tests/*-test.rkt`, mostly one per module (run an individual
file with `racket tests/<file>-test.rkt`): `lib`, `formulas`, `intro`, `prop`,
`defcnf`, `dp`, `stal`, `bdd`, `propexamples`, `fol`, `unif`, `skolem`, `herbrand`,
`tableaux`, `resolution`, `prolog`, `meson`, `skolems`, `provers`
(tableaux/resolution/prolog/meson), `pelletier` (Pelletier's problems through the
provers), `equality` (equal/cong/rewrite/order), `completion`
(completion/eqelim/paramodulation), `decidable`, `chapter5b`
(geom/interpolation/combining), `lcf`, `lcf-kernel`, `lcf-prover`,
`lcf-limitations`, and `extras`.

Run the whole suite with `raco test tests/` (1573 checks) — this recurses into
`tests/property/` and includes the property suite. CI runs only the `*-test.rkt`
unit suite (1300 checks); the `tests/property/` suite is local-only (it needs the
extra `rackcheck` package).

The `tests/property/` directory holds the
[rackcheck](https://docs.racket-lang.org/rackcheck/) property-based tests: a
`*-props.rkt` file per module group, all sharing a `common.rkt` of generators,
oracles, and configs. 273 properties (most run 400–1500 random cases) span every
chapter, checking each function against a trusted oracle or its defining law:

- **lib/formulas/intro** — set/union-find axioms (commutativity, associativity,
  absorption, transitivity), finite-partial-function and `valmod` laws,
  subset/power-set/`allsets` cardinalities, constructor/destructor round-trips, and
  that the expression simplifier, parser precedence, and parse∘print preserve value.
- **propositional/SAT** — every tautology checker (`tautology`/`bddtaut`/`ebddtaut`/
  `dptaut`/`dplltaut`/`dplbtaut`) and satisfiability checker agree with the
  truth-table oracle; NNF/NENF/DNF/CNF/`psimplify` preserve meaning; `eval` is a
  homomorphism; `dual` is involutive; Stålmarck is sound; the DP/DPLL rules
  (unit/pure-literal/resolution) preserve satisfiability; definitional CNF
  (`defcnf`/`defcnf3`) is equisatisfiable with 3-CNF clause bounds; `prime`/`ramsey`/
  adders/`bit`/`bitlength` match `prime?`, R(3,3)=6, validity, and native arithmetic.
- **BDD** — canonicity (equal nodes ⟺ logical equivalence), the diagram evaluates
  to the truth table, complement-edge negation, and the `bdd-and/or/imp/iff`
  combinators match formula construction.
- **first-order** — `simplify`/`nnf`/`prenex`/`pnf` preserve truth in random finite
  models and are idempotent; unification is sound, symmetric, and idempotent;
  `herbrand` ground terms stay ground; Skolemization removes existentials;
  MESON/tableaux/resolution/prolog prove propositional tautologies.
- **equality/ordering** — LPO is a strict order with the subterm property; rewriting
  computes the right number and is idempotent; congruence closure decides ground
  equational validity; completion's `renamepair`/`normalize-and-orient`/`interreduce`
  invariants hold; paramodulation proves reflexivity/symmetry/transitivity/congruence.
- **decidable theories** — the `complex`/`grobner`/`real` polynomial rings satisfy
  the ring/derivative laws (commutativity, distributivity, product rule); Cooper
  linear-arithmetic and monomial-order laws hold; QE decides ground (in)equalities;
  DLO QE eliminates all quantifiers; `grobner-decide` confirms field congruences;
  `alltuples`/`allmappings` cardinalities, Craig interpolation, and `homogenize`
  free-variable preservation hold.
- **LCF/limitations** — kernel-derived rules produce the expected theorems and the
  axiom-scheme side conditions hold exactly when their variable conditions do;
  `lcftaut` succeeds exactly on tautologies; `robeval`/`dholds`/`dtermval` agree
  with native arithmetic; Gödel numbering (`pair`/`gterm`/`gform`) is injective; the
  Turing tape round-trips.

## Status

The whole book is ported: all of chapters 1–7. One deliberate omission — since
this port uses s-expressions as the AST and has no concrete-syntax (`<<...>>`)
parser, the `limitations` module covers the chapter's computational content
(Goedel numbering, diagonalization, the Δ-decision procedure, Σ/Π/Δ
classification, Σ₁ verification, Turing machines, and Robinson ground-term
evaluation) but omits the parser-dependent Robinson-arithmetic provability
*demonstration* (`robinson_thm`, `sigma_prove`, …), which is ~250 lines of tactic
proofs whose every axiom/lemma is a parsed string.
