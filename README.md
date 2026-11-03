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

Names: a declaration keeps its qualified Unit name, quoted (`{|Prelude.sym|}`);
a constructor is `{|D.c|}`.

## What is not translated yet

- Records declared with `record` (`new`, segment types, derived members):
  much of `core/` builds on them (`PCtx`, `PTy`, `Ob`), and everything
  using them is left out for now.
- Level constraints (`constraint a <= l`) and constraint products are
  dropped; the plan is to encode `a <= l` by writing `l` as `lmax a l'`.
- Conversion that Unit has and the encoding only partly has: eta for Sigma
  on neutral terms (Dedukti has only the rule `pair (fst p) (snd p) --> p`).
- `dk` does not check that a lift goes upwards (`lift l m : U l -> U m`):
  the translator emits only the lifts Unit's own check justifies.
