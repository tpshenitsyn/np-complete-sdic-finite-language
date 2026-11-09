# A Lean formalization of the reduction from SCS to site-directed insertion closure

This repository formalizes a many-one reduction from shortest common
supersequence (SCS) over a five-letter alphabet to membership in the
site-directed insertion closure of a fixed finite seed language.
The size parameter is encoded in unary. The construction, both directions of
correctness, and a linear bound in the explicit transducer cost model are
proved in [`SupersequenceReduction.lean`](SupersequenceReduction.lean).

## Build

Install [Elan](https://github.com/leanprover/elan) and run `lake build` from the
repository root. The `lean-toolchain` file pins Lean 4.19.0. The proof imports
`Std`, which comes with Lean. You can also check the source directly.

```sh
lean -j 1 -s 65536 SupersequenceReduction.lean
```

The larger stack supports the finite certificates checked during elaboration.
The two `#print axioms` commands at the end of the source audit the final
theorems.

## Source and target problems

A word is a finite sequence of letters. Juxtaposition denotes concatenation,
and ε denotes the empty word. A word *a* is a subsequence of *b* if deleting
zero or more positions of *b* yields *a* without changing the order of the
remaining positions. The SCS instance consists of a nonempty list of words
`rows` over a five-letter alphabet and a natural number `p`. A witness is a
word of length exactly `p` that contains every row as a subsequence. This is
equivalent to asking for a witness of length at most `p`, since any shorter
witness can be padded with an arbitrary source letter.

```lean
structure Instance where
  rows : List (List Base)
  rows_nonempty : rows ≠ []
  p : Nat

def SCS (i : Instance) : Prop :=
  ∃ b : List Base, b.length = i.p ∧ ∀ a ∈ i.rows, a.Sublist b
```

For site-directed insertion, let the host be `x = x₁ u v x₂` and the donor
be `y = u z v`. The nonempty words `u` and `v` are the anchors. The
operation inserts `z` between their adjacent occurrences in the host and
produces `x₁ u z v x₂`. The words `x₁`, `x₂`, and `z` may be empty.
The closure of a seed language is the least language that contains the seeds
and is closed under insertion with both the host and the donor drawn from it.
In Lean, the two constructors give the base case and the insertion step of
a finite derivation.

```lean
inductive Closure (L : List Word) : Word → Prop where
  | seed {w} : w ∈ L → Closure L w
  | insert {x y x₁ x₂ u v z} : Closure L x → Closure L y →
      u ≠ [] → v ≠ [] → x = x₁ ++ u ++ v ++ x₂ → y = u ++ z ++ v →
      Closure L (x₁ ++ u ++ z ++ v ++ x₂)
```

## Alphabet, seed language, and reduction

The definitions in this section are in the namespace `SupersequenceReduction`.
The `some` and `none` constructors occur at two different option types.

| Mathematical object or operation | Lean definition |
| --- | --- |
| Five-letter source alphabet | `Base := Fin 5`. |
| Extended alphabet obtained by adjoining a fresh letter σ | `Letter := Option Base`. The original letter `a` becomes `some a`, and σ is `none : Letter`. The list `letters` starts with σ and continues with the five original letters in order. |
| Insertion alphabet and words | `Symbol` contains `A`, `B a`, `C`, `Ap`, `Bp a`, `Cp`, `extraB`, and the punctuation `dollar`, `sharp`, `flat`, `natural`, `heart`, `diamond`, `spade`, and `club`. Here `a : Letter`. The type of words is `Word := List Symbol`. Empty word, concatenation, and reversal are `[]`, `++`, and `List.reverse`. |
| Left encoding of an extended word | `h a := a.flatMap fun c => [A, B c, C]`. Each letter becomes one three-symbol block in the original order. |
| Reversed right encoding of an extended word | `hr a := a.reverse.flatMap fun c => [Cp, Bp c, Ap]`. The blocks are primed and occur in reverse letter order. |
| Mask payload of size `n` | `theta n := extraB :: (letters.take n).map Bp`. For `1 ≤ n ≤ 6`, the `Bp` symbols in this payload allow the first `n` extended letters. |
| A singleton or wildcard block | `Block := Option Letter`. The function `block` encloses the payload between `Cp` and `Ap`. Its payload is `[Bp c]` for `some c` and `theta 6` for `none : Block`. |
| Row marking | `markedRows i := i.rows.map fun a => a.map some ++ [none]`. Each row is lifted to the extended alphabet and ends in σ. |
| Target framing | `frame rows beta bs` starts with `[heart, dollar]`, writes each encoded row followed by `[sharp, dollar]`, then writes `[flat] ++ hr beta`. It writes the blocks of `bs` in reverse order, prefixing each with `[spade, club]`, and finishes with `[spade, club, natural, diamond]`. |
| Fixed seed language | `seeds : List Word` enumerates the words in the table below. Membership in this list supplies the base cases of `Closure`. |

Here `a` and `b` range over `letters`, and `n` ranges from 1 through 6.
For extended words `u` and `v`, the core encoding `Completion.core u v` is
`[dollar] ++ h u ++ [sharp, flat] ++ hr v ++ [natural]`. The table writes
`core` for this encoding.

| Seed family | Words in Lean notation |
| --- | --- |
| Envelope | `[heart, dollar, natural, diamond]` |
| Core words | `core [a] [a]`, `core [a] [a,b]`, `core [a] [b,a]` |
| Six phase donors for each `a` | `[B a, C, A, sharp, flat, Cp]`, `[A, sharp, flat, Ap, Cp, Bp a]`, `[C, A, B a, sharp, flat, Ap]`, `[B a, sharp, flat, Bp a, Ap, Cp]`, `[A, B a, C, sharp, flat, Bp a]`, `[C, sharp, flat, Cp, Bp a, Ap]` |
| Row-joining donor | `h [a] ++ [sharp, dollar, flat] ++ hr [b]` |
| Right-hand donors | `hr [a,b] ++ [Cp]`, `hr [a] ++ [spade, club] ++ hr [b] ++ [spade, club]`, `hr [a] ++ [spade, club, natural, diamond]` |
| Mask donors | `[club, Cp] ++ theta n ++ [Ap, spade]` |

The target contains the marked rows, a fixed σ block in the right encoding,
and `p` wildcard blocks.

```lean
def reduce (i : Instance) : Word :=
  frame (markedRows i) [none] (List.replicate i.p none)
```

## Unary encoding and time bound

`Input` has constructors `start`, `letter a`, `endRow`, `divider`,
`tick`, and `finish`. The function `input` encodes the rows using
`letter` and `endRow`, and writes the bound as `p` copies of `tick`
after the divider. The following table lists the fixed output for each input
symbol.

| Input symbol | Output `emit` |
| --- | --- |
| `start` | `[heart, dollar]` |
| `letter a` | `[A, B (some a), C]` |
| `endRow` | `h [none] ++ [sharp, dollar]` |
| `divider` | `[flat] ++ hr [none]` |
| `tick` | `[spade, club] ++ block none` |
| `finish` | `[spade, club, natural, diamond]` |

The output `translate s := s.flatMap emit` concatenates the emissions.
The relation `Runs s w t` means the transducer emits `w` on input `s`
at cost `t`. Its empty run costs zero. Its read rule prefixes the emission
and charges one step to read the input symbol plus one step for each output
symbol. The function `steps` computes that cost by recursion on the input.

```lean
def steps : List Input → Nat
  | [] => 0
  | c :: s => 1 + (emit c).length + steps s
```

Each emission contains at most eleven symbols. The factor of twelve in
`ReductionClaim` bounds the streaming transducer's time in this model.

## Proof outline

1. **From a common supersequence to a derivation.**
   `Completion.scs_implies_membership` appends σ to the witness and to each
   row. The construction builds a core word for each row and joins the cores
   into one frame. It moves the witness's original letters into singleton
   blocks and then masks them, yielding exactly `reduce i`.
2. **From a derivation to a common supersequence.**
   `TokenState.generated_rows` inducts over `Closure` derivations. It
   classifies donors by their endpoints, checks the finite local phase cases,
   and proves preservation for insertions at arbitrary positions. The
   invariant on a row word records its rows, its phase at the left–right
   junction, and a parsed right tail. A single word decoded from that tail
   contains every row as a subsequence.
3. **Readout and cost.**
   `TokenState.invariant_target_sound` recovers the original marked rows and
   the exact block sequence from the literal target. The readout removes σ
   and pads to length `p` if any wildcard block was decoded as σ.
   `implementation_certificate` proves the transducer computes the target
   and satisfies the time bound.

| Operation used in the converse | Lean definition |
| --- | --- |
| Enumerate possible anchor cuts for the finite checks | `FiniteCases.cuts` lists each prefix/suffix split using `take` and `drop`. `FiniteCases.inserts` uses these cuts to enumerate the results for a given host and donor. |
| Record partial blocks at the active junction | `PhaseCases.Phase` has six stages. `phaseLeft` and `phaseRight` give their partial encodings, and `advance` describes the next local window. |
| Parse the right tail | `TailTokens.Token` is a block with a payload, a spade, or a club. `TailTokens.encode` concatenates their codes. `TailTokens.blockLists` extracts the allowed letters of each block from its `Bp` symbols and skips separators. |
| Choose a letter from each block | `Soundness.Chooses` relates a list of allowed-letter lists to the word obtained by selecting one member of each list in order. |
| Require a shared witness | `TailTokens.Good rows ts` uses `Soundness.Good` on the reversed list of block choices. It requires a single decoded word containing every row as a subsequence. `TailTokens.good_monotone` extends that witness along a subsequence embedding of complete encoded tails. |
| Express the invariant on a generated row word | `TokenState.Invariant w := ∃ s, Valid s ∧ w = word s`. The state records the outer frame flag, preceding rows, last row, optional phase, and tail tokens. `TokenState.Valid` requires the row and tail conditions and the shared witness. |

## Theorems

The following declarations are in the namespace `SupersequenceReduction`.

```lean
theorem reduction_correct (i : Instance) : SCS i ↔ Closure seeds (reduce i)
theorem reduction_claim : ReductionClaim
```

`ReductionClaim` combines the equivalence with
`Runs (input i) (reduce i) (steps (input i))` for every instance and
`steps s ≤ 12 * s.length` for every transducer input.
