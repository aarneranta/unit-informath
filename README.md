# unit-informath
Informalization of Thierry Coquand's Unit project, https://github.com/coquand/unit

The first step is a translation of Unit to Dedukti, so that Informath can
read the developments as it reads other Dedukti code. `unit2dk` translates a
Unit program (a `.seg` file with its imports) to one Dedukti file, which
`dk check --eta` checks, and a `.dkgf` file with `#STRUCTURE` lines that
record Unit's segments.

## Building and running

The translator uses Unit's own checker as a library and Informath's Dedukti
syntax, from the sibling checkouts `../unit` and `../informath`.

    cabal build
    $(cabal list-bin unit2dk) ../unit/core/All.seg -dkgf=out/core.dkgf > out/core.dk 2> out/core.log
    dk check --eta out/core.dk
    python3 scripts/dkcheck_all.py out/core.dk     # dk declaration by declaration

`-units=N` translates only the first N top-level units (`-units=2`: `Base`
and `Prelude`). The summary on stderr counts the declarations translated in
full, the definitions given as axioms of their type, and those left out, each
with the reason. `scripts/dkcheck_all.py` checks the output with `dk`, turns
the declaration at each error into an axiom of its type (or drops its rules)
and starts again, so that it reports how many declarations `dk` accepts.

## The translation

The translator follows the checker through the program, with the hidden
arguments filled (`Seg.checkUnitsF`), and reads Unit's values back into
Dedukti terms, typed: a constructor gets the arguments of its data type, a
pair its Sigma type, a type used in a higher universe its lift. Definitions
stay folded: a value refers to a definition by its name, never by its body.

The encoding is in `prelude.dk`, printed at the head of the output:

- **Levels**: `Lvl` with `lz`, `ls` and an associative, commutative,
  idempotent `lmax` (Dedukti's `defac`), with the rules that normalise
  levels as Unit's `Level.hs` does.
- **Universes**, a la Tarski: `U l` the codes of the types in Unit's `U l`,
  `El l` their decoding, `u l : U (ls l)`. Cumulativity is
  `lift l m : U l -> U m`, inserted where Unit uses `U l <= U m`. A code is
  kept at its least level with one lift outside: rewrite rules move lifts
  out of `pi`, `sigma`, `id` and the terms that carry types, so that a type
  has one code at whatever level it is used.
- **Pi and Sigma** as codes with their two parts at their own levels; pairs,
  projections and surjective pairing. A record type `sig { .. }` is a chain
  of sigmas ending in `one`.
- **Identity types**: `id`, `refl`, and `J` computing on `refl`.
- **Data types**: a constant for the type and one for each constructor. A
  definition by `split` (which Unit allows only as the body of a definition,
  after its lambdas) is a constant with one rewrite rule per path through
  its branches; the recursive results `| r` are recursive calls.
- **Segments**, by lambda lifting: each member of `module M (params) {..}` is
  a constant taking the parameters (levels and terms) declared before it, and
  `M[args].f` is that constant applied to `args`. The `.dkgf` output has a
  line `#STRUCTURE M (params) members` for each segment. Local definitions
  (`where`) are unfolded where they are used.
- **Records** (`record R (heads) { fields ; derived members }`, Unit's
  doc/RECORDS.md): a constant `R : (params) (heads) -> U l`, a constructor
  `R.mk` taking the fields, and for each field `x` a selector
  `R.x : (params) (heads) -> (t : El l (R ..)) -> A`, in whose type the
  earlier fields are their selectors at `t`, defined by the rule
  `R.x .. (R.mk .. x1 .. xn) --> x`. A derived member is a definition taking
  the element as its last parameter. `new R[..]` is `R.mk` applied to the
  parameters and fields, `t.x` the selector applied to `t`. Records are
  nominal and have no eta in Unit, so neither here. The `.dkgf` output has a
  line `#RECORD R R.mk selectors` for each record, for Informath to read
  the constructor as a structure definition.
- **Records with fixed fields** (`R[ps][x := e]`, RECORDS.md §4, as
  `isEquiv A B f = IsEquiv[A, B, f]`): a record of their own,
  `{|R[x]|}`, whose parameters are those of `R` and the fixed fields, and
  whose fields are the others, with its constructor and selectors, and a
  coercion `{|R[x].up|}` to `R` (its rule gives `R.mk` with all the fields),
  inserted where Unit uses an element of `R[ps][x := e]` as one of `R[ps]`
  (subsumption, which Unit has without a coercion). A projection of a fixed
  field is its value. The variants a program uses are found by translating
  it: one not declared yet is asked for, and the program is translated
  again with it declared after its record.

Names: a declaration keeps its qualified Unit name, quoted (`{|Prelude.sym|}`);
a constructor is `{|D.c|}`.

## What is not translated yet

- Indexed inductive families (`data D (ps) : (is : Ixs) -> U l`), in Unit
  since 5 November: their declarations and the splits on them become axioms.
- Level constraints (`constraint a <= l`) and constraint products are
  dropped; the plan is to encode `a <= l` by writing `l` as `lmax a l'`.
- Conversion that Unit has and the encoding only partly has: eta for Sigma
  on neutral terms (Dedukti has only the rule `pair (fst p) (snd p) --> p`).
- `dk` does not check that a lift goes upwards (`lift l m : U l -> U m`):
  the translator emits only the lifts Unit's own check justifies.
