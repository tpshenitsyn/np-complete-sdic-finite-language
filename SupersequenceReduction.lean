import Std
set_option Elab.async false
section

/-!
Complete correctness proof of the supersequence reduction for the repaired
finite site-directed insertion seed language. Lean 4.19.0; Std only.

Definitions and the precise reduction statement are in Sections 1 and 2.
The final theorems `reduction_correct` and `reduction_claim` prove both
directions and certify the explicit linear-time unary-input transducer.

The converse uses a common-witness invariant and groups donor cases by
endpoints. It proves correctness of the reduction without claiming exact
equality between the closure and the paper's thirteen-type language.

Check: lean -j 1 -s 65536 SupersequenceReduction.lean
-/
namespace SupersequenceReduction

/- ========================= 1. DEFINITIONS ========================= -/

abbrev Base := Fin 5
abbrev Letter := Option Base       -- `none` is the fresh letter sigma.
abbrev Block := Option Letter      -- `none` is the full wildcard theta_6.

inductive Symbol where
  | A | B (a : Letter) | C | Ap | Bp (a : Letter) | Cp | extraB
  | dollar | sharp | flat | natural | heart | diamond | spade | club
  deriving DecidableEq, Repr
open Symbol
abbrev Word := List Symbol

def letters : List Letter := none :: (List.ofFn fun a : Base => some a)
def h (a : List Letter) : Word := a.flatMap fun c => [A, B c, C]
def hr (a : List Letter) : Word := a.reverse.flatMap fun c => [Cp, Bp c, Ap]
def theta (n : Nat) : Word := extraB :: (letters.take n).map Bp
def block (b : Block) : Word :=
  [Cp] ++ (match b with | none => theta 6 | some c => [Bp c]) ++ [Ap]

-- The exact type-12 frame, with blocks listed in decoded (unreversed) order.
def frame (rows : List (List Letter)) (beta : List Letter) (bs : List Block) : Word :=
  [heart, dollar] ++ rows.flatMap (fun a => h a ++ [sharp, dollar]) ++
  [flat] ++ hr beta ++ bs.reverse.flatMap (fun b => [spade, club] ++ block b) ++
  [spade, club, natural, diamond]

-- The repaired finite seed language in the revised TeX file, literally enumerated.
def seeds : List Word :=
  let core a b := [dollar] ++ h [a] ++ [sharp, flat] ++ hr b ++ [natural]
  [[heart, dollar, natural, diamond]] ++ letters.flatMap (fun a =>
    [core a [a], [B a, C, A, sharp, flat, Cp], [A, sharp, flat, Ap, Cp, Bp a],
     [C, A, B a, sharp, flat, Ap], [B a, sharp, flat, Bp a, Ap, Cp],
     [A, B a, C, sharp, flat, Bp a], [C, sharp, flat, Cp, Bp a, Ap],
     hr [a] ++ [spade, club, natural, diamond]] ++ letters.flatMap (fun b =>
       [core a [a,b], core a [b,a], hr [a,b] ++ [Cp],
        h [a] ++ [sharp, dollar, flat] ++ hr [b],
        hr [a] ++ [spade, club] ++ hr [b] ++ [spade, club]])) ++
  (List.ofFn fun i : Fin 6 => [club, Cp] ++ theta (i.val + 1) ++ [Ap, spade])

inductive Closure (L : List Word) : Word → Prop where
  | seed {w} : w ∈ L → Closure L w
  | insert {x y x₁ x₂ u v z} : Closure L x → Closure L y →
      u ≠ [] → v ≠ [] → x = x₁ ++ u ++ v ++ x₂ → y = u ++ z ++ v →
      Closure L (x₁ ++ u ++ z ++ v ++ x₂)

structure Instance where
  rows : List (List Base)
  rows_nonempty : rows ≠ []
  p : Nat

def SCS (i : Instance) : Prop :=
  ∃ b : List Base, b.length = i.p ∧ ∀ a ∈ i.rows, a.Sublist b
def markedRows (i : Instance) := i.rows.map fun a => a.map some ++ [none]
def reduce (i : Instance) : Word :=
  frame (markedRows i) [none] (List.replicate i.p none)

-- A fixed, one-state letter-to-word transducer. Its input encodes p in UNARY.
inductive Input where
  | start | letter (a : Base) | endRow | divider | tick | finish
  deriving DecidableEq
def input (i : Instance) : List Input :=
  [.start] ++ i.rows.flatMap (fun a => a.map Input.letter ++ [.endRow]) ++
  [.divider] ++ List.replicate i.p .tick ++ [.finish]
def emit : Input → Word
  | .start => [heart, dollar]
  | .letter a => [A, B (some a), C]
  | .endRow => h [none] ++ [sharp, dollar]
  | .divider => [flat] ++ hr [none]
  | .tick => [spade, club] ++ block none
  | .finish => [spade, club, natural, diamond]
def translate (s : List Input) : Word := s.flatMap emit

-- Primitive transducer cost: one input read and one step per output symbol.
-- This is streaming-machine time, not the runtime of Lean's list evaluator.
def steps : List Input → Nat
  | [] => 0
  | c :: s => 1 + (emit c).length + steps s

-- Big-step semantics of that transducer; each fixed emission is a finite path.
inductive Runs : List Input → Word → Nat → Prop where
  | done : Runs [] [] 0
  | read {s w t} (c : Input) : Runs s w t →
      Runs (c :: s) (emit c ++ w) (1 + (emit c).length + t)

/- ======================== 2. RESULT STATEMENT ======================= -/

/-- A many-one reduction with an explicit linear-time implementation.
The three conjuncts give computation, correctness, and a runtime bound.
Linear time implies polynomial time in the unary input encoding above. -/
-- Proved by `reduction_claim` at the end of this file.
def ReductionClaim : Prop :=
  (∀ i, Runs (input i) (reduce i) (steps (input i))) ∧
  (∀ i, SCS i ↔ Closure seeds (reduce i)) ∧
  (∀ s, steps s ≤ 12 * s.length)

/- =================== 3. SHORT AUXILIARY PROOFS ====================== -/

private theorem computes (i : Instance) : translate (input i) = reduce i := by
  have row (a : List Base) :
      (a.map Input.letter ++ [Input.endRow]).flatMap emit =
        h (a.map some ++ [none]) ++ [sharp, dollar] := by
    induction a with
    | nil => simp [emit, h]
    | cons a tail ih =>
        simpa [emit, h, List.append_assoc] using
          congrArg (fun w => [A, B (some a), C] ++ w) ih
  simp [translate, input, reduce, frame, markedRows, List.flatMap_append,
    List.flatMap_map, List.flatMap_assoc, row, List.flatMap_replicate, emit, List.append_assoc]

private theorem time_bound (s : List Input) : steps s ≤ 12 * s.length := by
  have bound (c : Input) : (emit c).length ≤ 11 := by
    cases c <;> simp [emit, h, hr, block, theta, letters]
  induction s with
  | nil => simp [steps]
  | cons c s ih =>
    have := bound c
    simp only [steps, List.length_cons]
    omega

private theorem execution (s : List Input) : Runs s (translate s) (steps s) := by
  induction s with
  | nil => exact .done
  | cons c s ih => exact .read c ih

/-- Unconditional checked implementation and runtime bound. -/
theorem implementation_certificate :
    (∀ i, Runs (input i) (reduce i) (steps (input i))) ∧
    (∀ s, steps s ≤ 12 * s.length) := by
  refine ⟨fun i => ?_, time_bound⟩
  rw [← computes i]
  exact execution _

end SupersequenceReduction

open SupersequenceReduction SupersequenceReduction.Symbol
namespace Completion

theorem letter_mem (a : Letter) : a ∈ letters := by
  cases a with
  | none => simp [letters]
  | some a =>
    apply List.mem_cons_of_mem
    exact List.mem_ofFn.mpr ⟨a, rfl⟩

def core (a b : List Letter) : Word :=
  [dollar] ++ h a ++ [sharp, flat] ++ hr b ++ [natural]

theorem seed_one (a : Letter) : Closure seeds (core [a] [a]) := by
  apply Closure.seed
  simp only [seeds, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨a, letter_mem a, Or.inl (by simp [core])⟩)

theorem seed_pair_left (a b : Letter) : Closure seeds (core [a] [a,b]) := by
  apply Closure.seed
  simp only [seeds, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inr ⟨a, letter_mem a, Or.inr ⟨b, letter_mem b, ?_⟩⟩)
  simp [core]

theorem seed_pair_right (a b : Letter) : Closure seeds (core [a] [b,a]) := by
  apply Closure.seed
  simp only [seeds, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inr ⟨a, letter_mem a, Or.inr ⟨b, letter_mem b, ?_⟩⟩)
  simp [core]

def donors (a : Letter) : List Word :=
  [[B a, C, A, sharp, flat, Cp], [A, sharp, flat, Ap, Cp, Bp a],
   [C, A, B a, sharp, flat, Ap], [B a, sharp, flat, Bp a, Ap, Cp],
   [A, B a, C, sharp, flat, Bp a], [C, sharp, flat, Cp, Bp a, Ap]]

theorem donor_seed {a : Letter} {w : Word} (hw : w ∈ donors a) : Closure seeds w := by
  apply Closure.seed
  simp only [seeds, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inr ⟨a, letter_mem a, Or.inl ?_⟩)
  simp only [donors, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | hw | hw | hw | hw | hw <;> simp [hw]

theorem insert {pre u v post z : Word}
    (hx : Closure seeds (pre ++ u ++ v ++ post))
    (hy : Closure seeds (u ++ z ++ v)) (hu : u ≠ []) (hv : v ≠ []) :
    Closure seeds (pre ++ u ++ z ++ v ++ post) :=
  Closure.insert hx hy hu hv rfl rfl

end Completion
namespace Completion

def phase (a b : List Letter) (g₁ g₂ : Word) : Word :=
  [dollar] ++ h a ++ g₁ ++ [sharp, flat] ++ g₂ ++ hr b ++ [natural]

-- The six matched insertions in Step 1 of the revised English proof.
private theorem append_both (a b : List Letter) (c d e : Letter)
    (hx : Closure seeds (core (a ++ [c]) (b ++ [d]))) :
    Closure seeds (core (a ++ [c,e]) (b ++ [d,e])) := by
  have s₀ : Closure seeds (phase (a ++ [c]) (b ++ [d]) [] []) := by simpa [phase,core] using hx
  have s₁ : Closure seeds (phase (a ++ [c]) (b ++ [d]) [A] []) := by
    have q := insert (pre := [dollar] ++ h a ++ [A]) (u := [B c,C])
      (v := [sharp,flat,Cp]) (post := [Bp d,Ap] ++ hr b ++ [natural]) (z := [A])
      (by simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using s₀)
      (donor_seed (a := c) (by simp [donors])) (by simp) (by simp)
    simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using q
  have s₂ : Closure seeds (phase (a ++ [c]) (b ++ [d]) [A] [Ap]) := by
    have q := insert (pre := [dollar] ++ h (a ++ [c])) (u := [A,sharp,flat])
      (v := [Cp,Bp d]) (post := [Ap] ++ hr b ++ [natural]) (z := [Ap])
      (by simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using s₁)
      (donor_seed (a := d) (by simp [donors])) (by simp) (by simp)
    simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using q
  have s₃ : Closure seeds (phase (a ++ [c]) (b ++ [d]) [A,B e] [Ap]) := by
    have q := insert (pre := [dollar] ++ h a ++ [A,B c]) (u := [C,A])
      (v := [sharp,flat,Ap]) (post := hr (b ++ [d]) ++ [natural]) (z := [B e])
      (by simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using s₂)
      (donor_seed (a := e) (by simp [donors])) (by simp) (by simp)
    simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using q
  have s₄ : Closure seeds (phase (a ++ [c]) (b ++ [d]) [A,B e] [Bp e,Ap]) := by
    have q := insert (pre := [dollar] ++ h (a ++ [c]) ++ [A]) (u := [B e,sharp,flat])
      (v := [Ap,Cp]) (post := [Bp d,Ap] ++ hr b ++ [natural]) (z := [Bp e])
      (by simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using s₃)
      (donor_seed (a := e) (by simp [donors])) (by simp) (by simp)
    simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using q
  have s₅ : Closure seeds (phase (a ++ [c]) (b ++ [d]) [A,B e,C] [Bp e,Ap]) := by
    have q := insert (pre := [dollar] ++ h (a ++ [c])) (u := [A,B e])
      (v := [sharp,flat,Bp e]) (post := [Ap] ++ hr (b ++ [d]) ++ [natural]) (z := [C])
      (by simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using s₄)
      (donor_seed (a := e) (by simp [donors])) (by simp) (by simp)
    simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using q
  have q := insert (pre := [dollar] ++ h (a ++ [c]) ++ [A,B e]) (u := [C,sharp,flat])
    (v := [Bp e,Ap]) (post := hr (b ++ [d]) ++ [natural]) (z := [Cp])
    (by simpa [phase,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using s₅)
    (donor_seed (a := e) (by simp [donors])) (by simp) (by simp)
  simpa [core,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using q
end Completion
namespace Completion

private theorem type1_seed (a b : Letter) : Closure seeds (hr [a,b] ++ [Cp]) := by
  apply Closure.seed
  simp only [seeds, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inr ⟨a, letter_mem a, Or.inr ⟨b, letter_mem b, ?_⟩⟩)
  simp

private theorem insert_before_last (a b : List Letter) (c d e : Letter)
    (hx : Closure seeds (core a (b ++ [c,d]))) :
    Closure seeds (core a (b ++ [c,e,d])) := by
  have q := insert (pre := [dollar] ++ h a ++ [sharp,flat]) (u := [Cp,Bp d,Ap])
    (v := [Cp]) (post := [Bp c,Ap] ++ hr b ++ [natural]) (z := [Cp,Bp e,Ap])
    (by simpa [core,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using hx)
    (by simpa [hr] using type1_seed e d) (by simp) (by simp)
  simpa [core,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using q

private theorem append_right (a b : List Letter) (c d e : Letter)
    (hx : Closure seeds (core a (b ++ [c,d]))) :
    Closure seeds (core a (b ++ [c,d,e])) := by
  have q := insert (pre := [dollar] ++ h a ++ [sharp,flat]) (u := [Cp])
    (v := [Bp d,Ap,Cp]) (post := [Bp c,Ap] ++ hr b ++ [natural]) (z := [Bp e,Ap,Cp])
    (by simpa [core,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using hx)
    (by simpa [hr] using type1_seed d e) (by simp) (by simp)
  simpa [core,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using q

private theorem singleton_core (a : Letter) (b : List Letter) :
    Closure seeds (core [a] (b.reverse ++ [a])) := by
  induction b with
  | nil => simpa using seed_one a
  | cons c b ih =>
    cases b with
    | nil => simpa using seed_pair_right a c
    | cons d b =>
      simpa [List.reverse_cons,List.append_assoc] using
        insert_before_last [a] b.reverse d a c (by simpa [List.reverse_cons,List.append_assoc] using ih)

private theorem core_sublist_rev {a b : List Letter} (hab : a.Sublist b) :
    a ≠ [] → Closure seeds (core a.reverse b.reverse) := by
  induction hab with
  | slnil => simp
  | @cons a b c hab ih =>
    intro ha
    cases b with
    | nil => exact False.elim (ha (List.eq_nil_of_sublist_nil hab))
    | cons d b =>
      cases b with
      | nil =>
        have heq : a = [d] := hab.eq_of_length (by
          have hle : a.length ≤ 1 := by simpa using hab.length_le
          have hpos := List.length_pos_iff.mpr ha
          change a.length = 1
          omega)
        subst a
        simpa using seed_pair_left d c
      | cons e b =>
        simpa [List.reverse_cons,List.append_assoc] using
          append_right a.reverse b.reverse e d c (by simpa [List.reverse_cons,List.append_assoc] using ih ha)
  | @cons₂ a b c hab ih =>
    intro _
    cases a with
    | nil => simpa [List.reverse_cons] using singleton_core c b
    | cons d a =>
      cases b with
      | nil => simp at hab
      | cons e b =>
        simpa [List.reverse_cons,List.append_assoc] using
          append_both a.reverse b.reverse d e c (by simpa [List.reverse_cons,List.append_assoc] using ih (by simp))

-- Every one-row core with a nonempty subsequence is generated from the seeds.
theorem core_sublist {a b : List Letter} (hab : a.Sublist b) (ha : a ≠ []) :
    Closure seeds (core a b) := by
  simpa using core_sublist_rev hab.reverse (by simpa using ha)

end Completion
namespace Completion

private theorem snoc {α : Type} (l : List α) (hn : l ≠ []) :
    ∃ p a, l = p ++ [a] := by
  cases he : l.reverse with
  | nil => exact False.elim (hn (by simpa using congrArg List.reverse he))
  | cons a p =>
    exact ⟨p.reverse, a, by simpa using congrArg List.reverse he⟩

def rowsCore (rows : List (List Letter)) (beta : List Letter) : Word :=
  [dollar] ++ rows.flatMap (fun a => h a ++ [sharp,dollar]) ++ [flat] ++ hr beta ++ [natural]

private theorem type5_seed (a b : Letter) :
    Closure seeds (h [a] ++ [sharp,dollar,flat] ++ hr [b]) := by
  apply Closure.seed
  simp only [seeds, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inr ⟨a, letter_mem a, Or.inr ⟨b, letter_mem b, ?_⟩⟩)
  simp

private theorem add_dollar (a b : List Letter) (ha : a ≠ []) (hb : b ≠ [])
    (hx : Closure seeds (core a b)) : Closure seeds (rowsCore [a] b) := by
  obtain ⟨p,c,rfl⟩ := snoc a ha
  obtain ⟨q,d,rfl⟩ := snoc b hb
  have k := insert (pre := [dollar] ++ h p) (u := h [c] ++ [sharp])
    (v := [flat] ++ hr [d]) (post := hr q ++ [natural]) (z := [dollar])
    (by simpa [core,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using hx)
    (by simpa [h,hr,List.append_assoc] using type5_seed c d)
    (by simp [h]) (by simp)
  simpa [rowsCore,h,hr,List.flatMap_append,List.reverse_append,List.append_assoc] using k

-- Merge independently constructed rows using their common concrete witness.
private theorem all_rows (rows : List (List Letter)) (beta : List Letter)
    (hn : rows ≠ []) (ha : ∀ a ∈ rows, a ≠ [])
    (hab : ∀ a ∈ rows, a.Sublist beta) : Closure seeds (rowsCore rows beta) := by
  induction rows with
  | nil => contradiction
  | cons a rows ih =>
    have hna := ha a (by simp)
    have hb : beta ≠ [] := by
      intro hnil
      exact hna (List.eq_nil_of_sublist_nil (by simpa [hnil] using hab a (by simp)))
    have one := add_dollar a beta hna hb (core_sublist (hab a (by simp)) hna)
    cases rows with
    | nil => exact one
    | cons b rows =>
      have tail := ih (by simp) (fun c hc => ha c (by simp [hc]))
        (fun c hc => hab c (by simp [hc]))
      have k := insert (pre := [dollar] ++ h a ++ [sharp]) (u := [dollar])
        (v := [flat] ++ hr beta ++ [natural])
        (post := []) (z := (b :: rows).flatMap (fun c => h c ++ [sharp,dollar]))
        (by simpa [rowsCore,List.append_assoc] using one)
        (by simpa [rowsCore,List.append_assoc] using tail) (by simp) (by simp)
      simpa [rowsCore,List.append_assoc] using k

private theorem wrap (w : Word) (hx : Closure seeds ([dollar] ++ w ++ [natural])) :
    Closure seeds ([heart,dollar] ++ w ++ [natural,diamond]) := by
  have base : Closure seeds [heart,dollar,natural,diamond] :=
    .seed (by simp [seeds])
  have k := insert (pre := [heart]) (u := [dollar]) (v := [natural])
    (post := [diamond]) (z := w) base hx (by simp) (by simp)
  simpa using k

private theorem type9_seed (a : Letter) :
    Closure seeds (hr [a] ++ [spade,club,natural,diamond]) := by
  apply Closure.seed
  simp only [seeds, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inr ⟨a, letter_mem a, Or.inl ?_⟩)
  simp

private theorem frame_empty (rows : List (List Letter)) (beta : List Letter)
    (hn : rows ≠ []) (ha : ∀ a ∈ rows, a ≠ []) (hb : beta ≠ [])
    (hab : ∀ a ∈ rows, a.Sublist beta) : Closure seeds (frame rows beta []) := by
  have raw := all_rows rows beta hn ha hab
  have enveloped := wrap (rows.flatMap (fun a => h a ++ [sharp,dollar]) ++ [flat] ++ hr beta)
    (by simpa [rowsCore,List.append_assoc] using raw)
  cases beta with
  | nil => contradiction
  | cons c beta =>
    have k := insert
      (pre := [heart,dollar] ++ rows.flatMap (fun a => h a ++ [sharp,dollar]) ++ [flat] ++ hr beta)
      (u := hr [c]) (v := [natural,diamond]) (post := []) (z := [spade,club])
      (by simpa [hr,List.append_assoc] using enveloped)
      (by simpa [List.append_assoc] using type9_seed c) (by simp [hr]) (by simp)
    simpa [frame,hr,List.append_assoc] using k

private theorem type10_seed (a b : Letter) :
    Closure seeds (hr [a] ++ [spade,club] ++ hr [b] ++ [spade,club]) := by
  apply Closure.seed
  simp only [seeds, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inr ⟨a, letter_mem a, Or.inr ⟨b, letter_mem b, ?_⟩⟩)
  simp

private theorem rotate_marks (bs : List Block) :
    bs.flatMap (fun b => [spade,club] ++ block b) ++ [spade,club] =
    [spade,club] ++ bs.flatMap (fun b => block b ++ [spade,club]) := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      simpa [List.append_assoc] using
        congrArg (fun w => [spade,club] ++ block b ++ w) ih

private theorem frame_alt (rows : List (List Letter)) (beta : List Letter) (bs : List Block) :
    frame rows beta bs = [heart,dollar] ++ rows.flatMap (fun c => h c ++ [sharp,dollar]) ++
      [flat] ++ hr beta ++ [spade,club] ++
      bs.reverse.flatMap (fun c => block c ++ [spade,club]) ++ [natural,diamond] := by
  simp only [frame]
  have eqn := rotate_marks bs.reverse
  simpa [List.append_assoc] using congrArg
    (fun w => [heart,dollar] ++ rows.flatMap (fun c => h c ++ [sharp,dollar]) ++
      [flat] ++ hr beta ++ w ++ [natural,diamond]) eqn

private theorem move_first (rows : List (List Letter)) (beta : List Letter)
    (a b : Letter) (bs : List Block)
    (hx : Closure seeds (frame rows (a :: b :: beta) bs)) :
    Closure seeds (frame rows (b :: beta) (bs ++ [some a])) := by
  have k := insert
    (pre := [heart,dollar] ++ rows.flatMap (fun c => h c ++ [sharp,dollar]) ++ [flat] ++ hr beta)
    (u := hr [b]) (v := hr [a] ++ [spade,club])
    (post := bs.reverse.flatMap (fun c => block c ++ [spade,club]) ++ [natural,diamond])
    (z := [spade,club])
    (by simpa [frame_alt,hr,List.append_assoc] using hx)
    (by simpa [List.append_assoc] using type10_seed b a) (by simp [hr]) (by simp [hr])
  simpa [frame_alt,hr,block,List.reverse_append,List.flatMap_append,List.append_assoc] using k

-- Separate off the witness prefix, retaining a nonempty unmarked tail.
private theorem move_prefix (rows : List (List Letter)) (pref beta : List Letter)
    (hb : beta ≠ []) (bs : List Block)
    (hx : Closure seeds (frame rows (pref ++ beta) bs)) :
    Closure seeds (frame rows beta (bs ++ pref.map some)) := by
  induction pref generalizing bs with
  | nil => simpa using hx
  | cons a pref ih =>
    have hn : pref ++ beta ≠ [] := List.append_ne_nil_of_right_ne_nil _ hb
    cases he : pref ++ beta with
    | nil => exact False.elim (hn he)
    | cons b rest =>
      have moved := move_first rows rest a b bs (by simpa [he] using hx)
      have next := ih (bs ++ [some a]) (by simpa [he] using moved)
      simpa [List.append_assoc] using next

end Completion
namespace Completion

private theorem type13_seed (i : Fin 6) :
    Closure seeds ([club,Cp] ++ theta (i.val + 1) ++ [Ap,spade]) := by
  apply Closure.seed
  exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

-- First grow a singleton to its theta_i, then extend that payload to theta_6.
private theorem mask_one (a : Letter) (pre post : Word)
    (hx : Closure seeds (pre ++ [club,Cp,Bp a,Ap,spade] ++ post)) :
    Closure seeds (pre ++ [club] ++ block none ++ [spade] ++ post) := by
  obtain ⟨p,t,he⟩ := List.append_of_mem (letter_mem a)
  have hlen : p.length < 6 := by
    have h : letters.length = 6 := by decide
    rw [he] at h
    simp only [List.length_append,List.length_cons] at h
    omega
  have hp : theta (p.length + 1) = extraB :: (p.map Bp ++ [Bp a]) := by
    simp [theta,he,List.take_append,List.take_add]
  have ht : theta 6 = extraB :: (p.map Bp ++ Bp a :: t.map Bp) := by
    have hh : letters.take 6 = letters := by decide
    change extraB :: (letters.take 6).map Bp = _
    rw [hh,he]
    simp
  have s₁ := insert (pre := pre) (u := [club,Cp]) (v := [Bp a,Ap,spade])
    (post := post) (z := extraB :: p.map Bp)
    (by simpa [List.append_assoc] using hx)
    (by simpa [hp,List.append_assoc] using type13_seed ⟨p.length,hlen⟩)
    (by simp) (by simp)
  have s₂ := insert (pre := pre) (u := [club,Cp] ++ theta (p.length + 1))
    (v := [Ap,spade]) (post := post) (z := t.map Bp)
    (by simpa [hp,List.append_assoc] using s₁)
    (by simpa [hp,ht,List.append_assoc] using type13_seed ⟨5,by decide⟩)
    (by simp) (by simp)
  simpa [block,hp,ht,List.append_assoc] using s₂

private theorem mask_list (w : List Letter) (pre post : Word)
    (hx : Closure seeds (pre ++ w.flatMap (fun a => [club] ++ block (some a) ++ [spade]) ++ post)) :
    Closure seeds (pre ++ (List.replicate w.length (none : Block)).flatMap
      (fun b => [club] ++ block b ++ [spade]) ++ post) := by
  induction w generalizing pre with
  | nil => simpa using hx
  | cons a w ih =>
    have first := mask_one a pre
      (w.flatMap (fun c => [club] ++ block (some c) ++ [spade]) ++ post)
      (by simpa [block,List.append_assoc] using hx)
    simpa [List.replicate_succ,List.append_assoc] using
      ih (pre ++ [club] ++ block none ++ [spade]) (by simpa [List.append_assoc] using first)

private theorem rotate_spades (bs : List Block) :
    bs.flatMap (fun b => [spade,club] ++ block b) ++ [spade,club] =
    [spade] ++ bs.flatMap (fun b => [club] ++ block b ++ [spade]) ++ [club] := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simpa [List.append_assoc] using
      congrArg (fun w => [spade,club] ++ block b ++ w) ih

private theorem frame_spades (rows : List (List Letter)) (beta : List Letter) (bs : List Block) :
    frame rows beta bs = [heart,dollar] ++ rows.flatMap (fun c => h c ++ [sharp,dollar]) ++
      [flat] ++ hr beta ++ [spade] ++
      bs.reverse.flatMap (fun c => [club] ++ block c ++ [spade]) ++ [club,natural,diamond] := by
  have eqn := rotate_spades bs.reverse
  simpa [frame,List.append_assoc] using congrArg
    (fun w => [heart,dollar] ++ rows.flatMap (fun c => h c ++ [sharp,dollar]) ++
      [flat] ++ hr beta ++ w ++ [natural,diamond]) eqn

private theorem mask_frame (rows : List (List Letter)) (beta w : List Letter)
    (hx : Closure seeds (frame rows beta (w.map some))) :
    Closure seeds (frame rows beta (List.replicate w.length none)) := by
  have k := mask_list w.reverse
    ([heart,dollar] ++ rows.flatMap (fun c => h c ++ [sharp,dollar]) ++ [flat] ++ hr beta ++ [spade])
    [club,natural,diamond]
    (by simpa [frame_spades,← List.map_reverse,List.flatMap_map,List.append_assoc] using hx)
  simpa [frame_spades,List.append_assoc] using k

/- ==================== PROVED FORWARD DIRECTION ==================== -/

/-- Unconditional: construct an actual insertion derivation for every yes-instance. -/
theorem scs_implies_membership (i : Instance) (hs : SCS i) : Closure seeds (reduce i) := by
  obtain ⟨b,hb,ha⟩ := hs
  have hn : markedRows i ≠ [] := by simpa [markedRows] using i.rows_nonempty
  have hr : ∀ a ∈ markedRows i, a ≠ [] := by
    intro a ha
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp ha
    exact List.append_ne_nil_of_right_ne_nil _ (by simp)
  have he : ∀ a ∈ markedRows i, a.Sublist (b.map some ++ [none]) := by
    intro a ham
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ham
    exact (List.Sublist.map some (ha c hc)).append_right [none]
  have base := frame_empty (markedRows i) (b.map some ++ [none]) hn hr (by simp) he
  have moved := move_prefix (markedRows i) (b.map some) [none] (by simp) [] base
  simpa [reduce,hb] using mask_frame (markedRows i) [none] (b.map some) moved

#print axioms scs_implies_membership
end Completion

end

/- ================= INSERTION AND ENDPOINT LEMMAS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace FiniteCases

def ends (w : Word) := (w.head?, w.getLast?)
def cuts {α : Type} (w : List α) : List (List α × List α) :=
  (List.range (w.length + 1)).map fun n => (w.take n, w.drop n)

theorem cut_mem {α : Type} (a b : List α) : (a,b) ∈ cuts (a ++ b) := by
  apply List.mem_map.mpr
  refine ⟨a.length, List.mem_range.mpr (by simp; omega), ?_⟩
  simp

def inserts (x y : Word) : List Word :=
  (cuts x).flatMap fun (pre,s) =>
  if s.head? != y.head? then [] else
  (cuts y).flatMap fun (u,r) =>
  if u = [] then [] else
  if s.take u.length != u then [] else
  (cuts r).flatMap fun (_,v) =>
  if v = [] then [] else
  if (s.drop u.length).take v.length != v then [] else
    [pre ++ y ++ s.drop (u.length + v.length)]

theorem insert_mem (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ []) :
    pre ++ u ++ z ++ v ++ post ∈ inserts (pre ++ u ++ v ++ post) (u ++ z ++ v) := by
  apply List.mem_flatMap.mpr
  refine ⟨(pre,u ++ v ++ post), ?_, ?_⟩
  · simpa [List.append_assoc] using cut_mem pre (u ++ v ++ post)
  have hh : (u ++ v ++ post).head? = (u ++ z ++ v).head? := by
    cases u <;> simp_all
  simp only [hh,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply List.mem_flatMap.mpr
  refine ⟨(u,z ++ v), ?_, ?_⟩
  · simpa [List.append_assoc] using cut_mem u (z ++ v)
  have ht : (u ++ v ++ post).take u.length = u := by simp [List.append_assoc]
  simp only [hu,↓reduceIte,ht,bne_self_eq_false,Bool.false_eq_true]
  apply List.mem_flatMap.mpr
  refine ⟨(z,v), cut_mem z v, ?_⟩
  have hd : (u ++ v ++ post).drop (u.length + v.length) = post := by
    rw [← List.length_append,List.drop_left]
  have ht' : ((u ++ v ++ post).drop u.length).take v.length = v := by
    simp [List.append_assoc]
  simp [hv,ht',hd,List.append_assoc]

private theorem ends_insert (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ []) :
    ends (pre ++ u ++ z ++ v ++ post) = ends (pre ++ u ++ v ++ post) := by
  apply Prod.ext
  · cases pre <;> cases u <;> simp_all [ends]
  · have hv' : v.getLast? ≠ none := by simpa using hv
    cases hp : post.getLast? with
    | some a => simp [ends, List.getLast?_append, hp]
    | none =>
      cases he : v.getLast? with
      | none => exact (hv' he).elim
      | some a => simp [ends, List.getLast?_append, hp, he]

/-- Insertion preserves the host's two endpoint symbols. -/
theorem closure_ends {w : Word} (h : Closure seeds w) : ends w ∈ seeds.map ends := by
  induction h with
  | seed hw => exact List.mem_map.mpr ⟨_, hw, rfl⟩
  | @insert x y pre post u v z hx hy hu hv ex ey ihx ihy =>
    rw [ends_insert _ _ _ _ _ hu hv]
    simpa [ex] using ihx

-- The three finite donor families (types 4, 5, and 13).
def small : List Word :=
  letters.flatMap (fun a => Completion.donors a ++
    letters.map (fun b => h [a] ++ [sharp,dollar,flat] ++ hr [b])) ++
  (List.ofFn fun i : Fin 6 => [club,Cp] ++ theta (i.val+1) ++ [Ap,spade])


def pairs : Word → List (Option Symbol × Option Symbol)
  | [] => []
  | a :: w => w.map (fun b => (some a, some b)) ++ pairs w

private theorem pairs_mem {a b : Symbol} {w : Word}
    (h : [a,b].Sublist w) : (some a,some b) ∈ pairs w := by
  induction w with
  | nil => cases h
  | cons c w ih =>
    cases h with
    | cons _ h => exact List.mem_append_right _ (ih h)
    | cons₂ _ h =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨b, List.singleton_sublist.mp h, rfl⟩

theorem donor_ends_pair (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ []) :
    ends (u ++ z ++ v) ∈ pairs (pre ++ u ++ v ++ post) := by
  obtain ⟨a, us, rfl⟩ := List.exists_cons_of_ne_nil hu
  have hv' : v.getLast? ≠ none := by simpa using hv
  cases he : v.getLast? with
  | none => exact (hv' he).elim
  | some b =>
    obtain ⟨vs, rfl⟩ := List.getLast?_eq_some_iff.mp he
    have h : [a,b].Sublist (pre ++ (a :: us) ++ (vs ++ [b]) ++ post) := by
      have mid : [a,b].Sublist ((a :: us) ++ (vs ++ [b])) := by
        apply List.Sublist.cons₂
        exact List.singleton_sublist.mpr (by simp)
      simpa [List.append_assoc] using
        mid.trans ((List.sublist_append_right pre _).trans (List.sublist_append_left _ post))
    have eqn : ends ((a :: us) ++ z ++ (vs ++ [b])) = (some a,some b) := by
      simp only [ends, List.head?_append, List.head?_cons, Option.some_or]
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or]
    rw [eqn]
    exact pairs_mem h

end FiniteCases

end

/- ================= UNIQUE BORDERS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases
namespace Boundary

def headUnique : Word → Bool
  | [] => true
  | a :: w => !w.contains a

def uniqueEnds (w : Word) : Bool := headUnique w && headUnique w.reverse

private theorem prefix_empty (pre u rest : Word) (hu : u ≠ [])
    (hq : headUnique (pre ++ u ++ rest) = true)
    (hh : (pre ++ u ++ rest).head? = u.head?) : pre = [] := by
  cases pre with
  | nil => rfl
  | cons c pre =>
    cases u with
    | nil => exact (hu rfl).elim
    | cons a u =>
      simp only [List.cons_append,List.head?_cons,Option.some.injEq] at hh
      subst c
      simp [headUnique] at hq

/-- Unique border symbols force a matching-endpoint donor to replace the
whole host; this handles all B cases without enumerating anchor cuts. -/
theorem whole_host (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (hq : uniqueEnds (pre ++ u ++ v ++ post) = true)
    (he : ends (pre ++ u ++ v ++ post) = ends (u ++ z ++ v)) :
    pre ++ u ++ z ++ v ++ post = u ++ z ++ v := by
  have hq' : headUnique (pre ++ u ++ v ++ post) = true ∧
      headUnique (pre ++ u ++ v ++ post).reverse = true := by simpa [uniqueEnds] using hq
  have hhead : (pre ++ u ++ v ++ post).head? = u.head? := by
    have hh := congrArg Prod.fst he
    cases u <;> simp_all [ends]
  have hl : pre = [] := prefix_empty pre u (v ++ post) hu
    (by simpa [uniqueEnds,List.append_assoc] using hq'.1)
    (by simpa [List.append_assoc] using hhead)
  have hlast : (pre ++ u ++ v ++ post).getLast? = v.getLast? := by
    have hh := congrArg Prod.snd he
    have hv' : v.getLast? ≠ none := by simpa using hv
    cases ht : v.getLast? with
    | none => exact (hv' ht).elim
    | some a => simpa [ends,List.getLast?_append,ht] using hh
  have hr : post.reverse = [] := prefix_empty post.reverse v.reverse
    (u.reverse ++ pre.reverse) (by simpa using hv)
    (by simpa [uniqueEnds,List.reverse_append,List.append_assoc] using hq'.2)
    (by simpa only [List.reverse_append,List.append_assoc] using
      (show (pre ++ u ++ v ++ post).reverse.head? = v.reverse.head? by
        simpa only [List.head?_reverse] using hlast))
  have hp : post = [] := List.reverse_eq_nil_iff.mp hr
  simp [hl,hp]

end Boundary

end

/- ================= ALL GENERATED SHORT DONORS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace FiniteCases
def smallEnd : Option Symbol × Option Symbol → Bool
  | (some (B _), some Cp) | (some A, some (Bp _)) | (some C, some Ap)
  | (some A, some Ap) | (some club, some spade) => true
  | _ => false

def allEnd : Option Symbol × Option Symbol → Bool
  | (some heart,some diamond) | (some dollar,some natural) | (some Cp,some Cp)
  | (some Cp,some diamond) | (some Cp,some club) => true
  | p => smallEnd p

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem seeds_end_types : ∀ x ∈ seeds, allEnd (ends x) = true := by decide +kernel

private theorem closure_end_types {w : Word} (h : Closure seeds w) :
    allEnd (ends w) = true := by
  obtain ⟨x,hx,he⟩ := List.mem_map.mp (closure_ends h)
  rw [← he]
  exact seeds_end_types x hx

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem small_endpoint_filter :
    ∀ x ∈ small, ∀ p ∈ pairs x, allEnd p = true → smallEnd p = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seed_small_of_ends :
    ∀ x ∈ seeds, smallEnd (ends x) = true → x ∈ small := by
  decide +kernel



set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem small_unique : ∀ x ∈ small, Boundary.uniqueEnds x = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem mismatch_check :
    (small.all fun x => small.all fun y =>
      (ends x == ends y) || (inserts x y == [])) = true := by decide +kernel

private theorem no_mismatch : ∀ x ∈ small, ∀ y ∈ small,
    ends x = ends y ∨ inserts x y = [] := by
  have hc := mismatch_check
  simp only [List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hc
  exact hc

theorem small_insert_eq (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (hx : pre ++ u ++ v ++ post ∈ small) (hy : u ++ z ++ v ∈ small) :
    pre ++ u ++ z ++ v ++ post = u ++ z ++ v := by
  rcases no_mismatch _ hx _ hy with he | he
  · exact Boundary.whole_host _ _ _ _ _ hu hv (small_unique _ hx) he
  · have hi := insert_mem pre u v post z hu hv
    rw [he] at hi
    cases hi

/-- Exact finite classification for arbitrary generated short-endpoint donors. -/
theorem generated_small {w : Word} (h : Closure seeds w)
    (he : smallEnd (ends w) = true) : w ∈ small := by
  induction h with
  | seed hw => exact seed_small_of_ends _ hw he
  | @insert x y pre post u v z hx hy hu hv ex ey ihx ihy =>
    have eh : smallEnd (ends x) = true := by
      rw [ex]
      have hh : ends (pre ++ u ++ z ++ v ++ post) = ends (pre ++ u ++ v ++ post) := by
        apply Prod.ext
        · cases pre <;> cases u <;> simp_all [ends]
        · have hv' : v.getLast? ≠ none := by simpa using hv
          cases hp : post.getLast? with
          | some a => simp [ends,List.getLast?_append,hp]
          | none =>
            cases ht : v.getLast? with
            | none => exact (hv' ht).elim
            | some a => simp [ends,List.getLast?_append,hp,ht]
      simpa only [hh] using he
    have hxs := ihx eh
    have ep : ends y ∈ pairs x := by
      rw [ex,ey]
      exact donor_ends_pair _ _ _ _ _ hu hv
    have hys := ihy (small_endpoint_filter x hxs (ends y) ep (closure_end_types hy))
    rw [small_insert_eq _ _ _ _ _ hu hv (by simpa [ex] using hxs) (by simpa [ey] using hys)]
    simpa [ey] using hys

end FiniteCases

end

/- ================= PUNCTUATION ORDER ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace LocalSyntax

def Linked {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: w => R a b ∧ Linked R (b :: w)

private theorem linked_prefix {α : Type} {R : α → α → Prop}
    (a b : List α) (h : Linked R (a ++ b)) : Linked R a := by
  induction a with
  | nil => trivial
  | cons c a ih =>
    cases a with
    | nil => trivial
    | cons d a => exact ⟨h.1, ih h.2⟩

private theorem linked_suffix {α : Type} {R : α → α → Prop}
    (a b : List α) (h : Linked R (a ++ b)) : Linked R b := by
  induction a with
  | nil => exact h
  | cons c a ih =>
    cases he : a ++ b with
    | nil =>
      have hb : b = [] := (List.append_eq_nil_iff.mp he).2
      simp [hb, Linked]
    | cons d t =>
      apply ih
      simp only [List.cons_append, he] at h
      rw [he]
      exact h.2

private theorem linked_join {α : Type} {R : α → α → Prop}
    (x : List α) (a : α) (y : List α)
    (hx : Linked R (x ++ [a])) (hy : Linked R (a :: y)) :
    Linked R (x ++ a :: y) := by
  induction x with
  | nil => exact hy
  | cons b x ih =>
    cases x with
    | nil => exact ⟨hx.1,hy⟩
    | cons c x => exact ⟨hx.1,ih hx.2⟩

/-- Any condition on adjacent symbol pairs is preserved by insertion. -/
theorem linked_insert {α : Type} {R : α → α → Prop}
    (pre u v post z : List α) (hu : u ≠ []) (hv : v ≠ [])
    (hx : Linked R (pre ++ u ++ v ++ post)) (hy : Linked R (u ++ z ++ v)) :
    Linked R (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨a, us, rfl⟩ := List.exists_cons_of_ne_nil hu
  have hv' : v.getLast? ≠ none := by simpa using hv
  cases he : v.getLast? with
  | none => exact (hv' he).elim
  | some b =>
    obtain ⟨vs,rfl⟩ := List.getLast?_eq_some_iff.mp he
    have left : Linked R (pre ++ [a]) := linked_prefix (pre ++ [a])
      (us ++ vs ++ [b] ++ post) (by simpa [List.append_assoc] using hx)
    have right : Linked R (b :: post) := linked_suffix
      (pre ++ a :: us ++ vs) (b :: post) (by simpa [List.append_assoc] using hx)
    have mid := linked_join pre a (us ++ z ++ vs ++ [b]) left
      (by simpa [List.append_assoc] using hy)
    have result := linked_join (pre ++ a :: us ++ z ++ vs) b post
      (by simpa [List.append_assoc] using mid) right
    simpa [List.append_assoc] using result

def edges : Word → List (Symbol × Symbol)
  | [] => []
  | [_] => []
  | a :: b :: w => (a,b) :: edges (b :: w)

def allowed (a b : Symbol) : Prop := (a,b) ∈ seeds.flatMap edges

private theorem linked_edges (w : Word) : Linked (fun a b => (a,b) ∈ edges w) w := by
  induction w with
  | nil => trivial
  | cons a w ih =>
    cases w with
    | nil => trivial
    | cons b w =>
      constructor
      · simp [edges]
      · have mono : ∀ (t : Word), Linked (fun c d => (c,d) ∈ edges (b :: w)) t →
            Linked (fun c d => (c,d) ∈ edges (a :: b :: w)) t := by
          intro t ht
          induction t with
          | nil => trivial
          | cons c t it =>
            cases t with
            | nil => trivial
            | cons d t => exact ⟨List.mem_cons_of_mem _ ht.1, it ht.2⟩
        exact mono _ ih

private theorem linked_mono {α : Type} {R S : α → α → Prop}
    (h : ∀ a b, R a b → S a b) (w : List α) (hw : Linked R w) : Linked S w := by
  induction w with
  | nil => trivial
  | cons a w ih =>
    cases w with
    | nil => trivial
    | cons b w => exact ⟨h _ _ hw.1,ih hw.2⟩

/-- A checked local-syntax invariant for every generated word. -/
theorem closure_linked {w : Word} (h : Closure seeds w) : Linked allowed w := by
  induction h with
  | seed hw =>
    apply linked_mono (w := _) (hw := linked_edges _)
    intro a b hab
    exact List.mem_flatMap.mpr ⟨_,hw,hab⟩
  | @insert x y pre post u v z hx hy hu hv ex ey ihx ihy =>
    exact linked_insert pre u v post z hu hv (by simpa [ex] using ihx)
      (by simpa [ey] using ihy)


-- The unique punctuation has its own rank; left and right alphabets occupy
-- separate ranks. This rules out hidden extra junctions in generated words.
def rank : Symbol → Nat
  | heart => 0
  | A | B _ | C | dollar | sharp => 1
  | flat => 2
  | Ap | Bp _ | Cp | extraB | spade | club => 3
  | natural => 4
  | diamond => 5

def ordered (a b : Symbol) : Prop :=
  rank a < rank b ∨ (rank a = rank b ∧ (rank a = 1 ∨ rank a = 3))

private theorem ordered_trans {a b c : Symbol}
    (h : ordered a b) (k : ordered b c) : ordered a c := by
  unfold ordered at *
  omega

private theorem linked_pairwise {α : Type} {R : α → α → Prop}
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (w : List α) (h : Linked R w) : w.Pairwise R := by
  induction w with
  | nil => exact .nil
  | cons a w ih =>
    cases w with
    | nil => simp
    | cons b w =>
      have ht := ih h.2
      apply List.Pairwise.cons _ ht
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact trans h.1 ((List.pairwise_cons.mp ht).1 c hc)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem edges_ordered :
    ∀ p ∈ seeds.flatMap edges, ordered p.1 p.2 := by
  unfold ordered
  decide +kernel

/-- Every generated word has one left-to-right junction and correctly ordered
outer punctuation. Repeated flat/natural/heart/diamond symbols are impossible. -/
theorem closure_ordered {w : Word} (h : Closure seeds w) : w.Pairwise ordered :=
  linked_pairwise (R := ordered) (fun {_ _ _} h k => ordered_trans h k) w
    (linked_mono (fun a b hab => edges_ordered (a,b) hab) w (closure_linked h))

theorem unique_flat {w : Word} (h : Closure seeds w) : ¬ [flat,flat].Sublist w := by
  intro hs
  have bad := (List.pairwise_iff_forall_sublist.mp (closure_ordered h)) hs
  simp [ordered,rank] at bad

end LocalSyntax

end

/- ================= ALL GENERATED TYPE-1 DONORS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol LocalSyntax FiniteCases
namespace TypeOne

def basic : Symbol → Bool
  | Ap | Cp | Bp _ => true
  | _ => false

def next : Symbol → Symbol → Bool
  | Cp, Bp _ | Bp _, Ap | Ap, Cp => true
  | _, _ => false

def chain : Word → Bool
  | [] | [_] => true
  | a :: b :: w => next a b && chain (b :: w)

private theorem chain_iff (w : Word) : chain w = true ↔ Linked (fun a b => next a b = true) w := by
  induction w with
  | nil => simp [chain,Linked]
  | cons a w ih => cases w <;> simp_all [chain,Linked]

def Inv (w : Word) : Prop :=
  w.all basic = true ∧ chain w = true ∧ 7 ≤ w.length

private theorem ends_insert (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ []) :
    ends (pre ++ u ++ z ++ v ++ post) = ends (pre ++ u ++ v ++ post) := by
  apply Prod.ext
  · cases pre <;> cases u <;> simp_all [ends]
  · have hv' : v.getLast? ≠ none := by simpa using hv
    cases hp : post.getLast? with
    | some a => simp [ends,List.getLast?_append,hp]
    | none =>
      cases he : v.getLast? with
      | none => exact (hv' he).elim
      | some a => simp [ends,List.getLast?_append,hp,he]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem seeds_inv : ∀ w ∈ seeds, ends w = (some Cp,some Cp) → Inv w := by
  unfold Inv
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem ends_filter : ∀ p ∈ seeds.map ends,
    p.1.any basic = true → p.2.any basic = true → p = (some Cp,some Cp) := by
  decide +kernel

private theorem donor_ends_basic (pre u v post z : Word)
    (hu : u ≠ []) (hv : v ≠ []) (hx : (pre ++ u ++ v ++ post).all basic = true) :
    (ends (u ++ z ++ v)).1.any basic = true ∧
    (ends (u ++ z ++ v)).2.any basic = true := by
  obtain ⟨a,us,rfl⟩ := List.exists_cons_of_ne_nil hu
  have hv' : v.getLast? ≠ none := by simpa using hv
  cases he : v.getLast? with
  | none => exact (hv' he).elim
  | some b =>
    obtain ⟨vs,rfl⟩ := List.getLast?_eq_some_iff.mp he
    have ha : basic a = true := (List.all_eq_true.mp hx) a (by simp)
    have hb : basic b = true := (List.all_eq_true.mp hx) b (by simp)
    simp only [ends,List.head?_append,List.head?_cons,Option.some_or]
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
    simp [ha,hb]

/-- Every generated Cp-to-Cp donor consists of ordinary singleton blocks.
Its classification does not assume the 13-type closure theorem. -/
theorem generated_one {w : Word} (h : Closure seeds w)
    (he : ends w = (some Cp,some Cp)) : Inv w := by
  induction h with
  | seed hw => exact seeds_inv _ hw he
  | @insert x y pre post u v z hx hy hu hv ex ey ihx ihy =>
    have exend : ends x = (some Cp,some Cp) := by
      rw [ex]
      simpa only [ends_insert _ _ _ _ _ hu hv] using he
    have hxi := ihx exend
    have hab := donor_ends_basic pre u v post z hu hv (by simpa [ex] using hxi.1)
    have eyend : ends y = (some Cp,some Cp) :=
      ends_filter (ends y) (closure_ends hy) (by simpa [ey] using hab.1)
        (by simpa [ey] using hab.2)
    have hyi := ihy eyend
    refine ⟨?_,?_,?_⟩
    · have hp := hxi.1
      have hq := hyi.1
      rw [ex] at hp
      rw [ey] at hq
      simp only [List.all_append,Bool.and_eq_true] at hp hq ⊢
      exact ⟨⟨⟨⟨hp.1.1.1,hp.1.1.2⟩,hq.1.2⟩,hp.1.2⟩,hp.2⟩
    · apply (chain_iff _).mpr
      exact linked_insert _ _ _ _ _ hu hv
        (by simpa [ex] using (chain_iff _).mp hxi.2.1)
        (by simpa [ey] using (chain_iff _).mp hyi.2.1)
    · have hl := hxi.2.2
      simp only [ex,List.length_append] at hl ⊢
      omega


private theorem parse_cp (w : Word)
    (hc : Linked (fun a b => next a b = true) (Cp :: w))
    (he : (Cp :: w).getLast? = some Cp) :
    ∃ b : List Letter, Cp :: w = b.flatMap (fun a => [Cp,Bp a,Ap]) ++ [Cp] := by
  cases w with
  | nil => exact ⟨[],rfl⟩
  | cons s w =>
    have hs := hc.1
    cases s <;> simp [next] at hs
    case Bp a =>
      cases w with
      | nil => simp at he
      | cons s w =>
        have hs := hc.2.1
        cases s <;> simp [next] at hs
        case Ap =>
          cases w with
          | nil => simp at he
          | cons s w =>
            have hs := hc.2.2.1
            cases s <;> simp [next] at hs
            case Cp =>
              obtain ⟨b,hb⟩ := parse_cp w hc.2.2.2 (by simpa using he)
              refine ⟨a :: b,?_⟩
              simpa using congrArg (fun q => Cp :: Bp a :: Ap :: q) hb
termination_by w.length

/-- Exact type-1 shape, including the two-block lower bound. -/
theorem generated_one_shape {w : Word} (h : Closure seeds w)
    (he : ends w = (some Cp,some Cp)) :
    ∃ beta : List Letter, 2 ≤ beta.length ∧ w = hr beta ++ [Cp] := by
  have hi := generated_one h he
  have hh : w.head? = some Cp := congrArg Prod.fst he
  have hl : w.getLast? = some Cp := congrArg Prod.snd he
  obtain ⟨tail,rfl⟩ := List.head?_eq_some_iff.mp hh
  obtain ⟨b,hb⟩ := parse_cp tail ((chain_iff _).mp hi.2.1) hl
  refine ⟨b.reverse,?_,?_⟩
  · have len : (b.flatMap fun a => [Cp,Bp a,Ap]).length = 3 * b.length := by
      clear hb
      induction b with
      | nil => rfl
      | cons a b ih =>
        simp only [List.flatMap_cons,List.length_append,List.length_cons,List.length_nil,ih]
        omega
    have hlen := hi.2.2
    rw [hb] at hlen
    simp only [List.length_append,List.length_singleton,len] at hlen
    simp only [List.length_reverse]
    omega
  · simpa [hr] using hb

end TypeOne

end

/- ================= DONOR ENDPOINTS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases
namespace AlphabetInvariant

def endAllowed (p : Symbol → Bool) (w : Word) : Prop :=
  w.head?.any p = true ∧ w.getLast?.any p = true

theorem donor_allowed (p : Symbol → Bool) (pre u v post z : Word)
    (hu : u ≠ []) (hv : v ≠ []) (hx : (pre ++ u ++ v ++ post).all p = true) :
    endAllowed p (u ++ z ++ v) := by
  obtain ⟨a,us,rfl⟩ := List.exists_cons_of_ne_nil hu
  have hv' : v.getLast? ≠ none := by simpa using hv
  cases he : v.getLast? with
  | none => exact (hv' he).elim
  | some b =>
    obtain ⟨vs,rfl⟩ := List.getLast?_eq_some_iff.mp he
    have ha : p a = true := (List.all_eq_true.mp hx) a (by simp)
    have hb : p b = true := (List.all_eq_true.mp hx) b (by simp)
    simp only [endAllowed,List.head?_append,List.head?_cons,Option.some_or]
    simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
    simp [ha,hb]

end AlphabetInvariant

end

/- ================= DECODING A SHARED WITNESS ================= -/
section

open SupersequenceReduction SupersequenceReduction.Symbol
namespace Soundness

/- A payload is the nonempty list of letters allowed by one right-hand block.
   `none` below marks the end of a block, not the alphabet letter sigma. -/
def packed {α : Type} (bs : List (List α)) : List (Option α) :=
  bs.flatMap fun b => b.map some ++ [none]
def selected {α : Type} (w : List α) : List (Option α) :=
  w.flatMap fun a => [some a, none]

inductive Chooses {α : Type} : List (List α) → List α → Prop where
  | nil : Chooses [] []
  | cons {b bs a w} : a ∈ b → Chooses bs w → Chooses (b :: bs) (a :: w)

private theorem boundary_skip {α : Type} (b : List α)
    {s r : List (Option α)} (h : (none :: s).Sublist (b.map some ++ r)) :
    (none :: s).Sublist r := by
  induction b with
  | nil => simpa using h
  | cons a b ih =>
    cases h with
    | cons _ h => exact ih h

private theorem selected_skip_boundary {α : Type} (w : List α)
    {r : List (Option α)} (h : (selected w).Sublist (none :: r)) :
    (selected w).Sublist r := by
  cases w with
  | nil => simp [selected]
  | cons a w =>
    cases h with
    | cons _ h => exact h

private theorem first_payload {α : Type} (b : List α)
    (a : α) (w : List α) {r : List (Option α)}
    (h : (selected (a :: w)).Sublist (b.map some ++ r)) :
    (selected (a :: w)).Sublist r ∨
      (a ∈ b ∧ (selected w).Sublist r) := by
  induction b with
  | nil => exact Or.inl h
  | cons c b ih =>
    cases h with
    | cons _ h =>
      rcases ih h with h | ⟨hm, hs⟩
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_cons_of_mem _ hm, hs⟩
    | cons₂ _ h =>
      have hb := boundary_skip b h
      exact Or.inr ⟨by simp, (List.sublist_cons_self _ _).trans hb⟩

/-- Decode an embedding by choosing one letter in every new block.
The end markers force successive selected letters into distinct blocks. -/
theorem decode {α : Type} (bs : List (List α))
    (hn : ∀ b ∈ bs, b ≠ []) (w : List α)
    (h : (selected w).Sublist (packed bs)) :
    ∃ v, Chooses bs v ∧ w.Sublist v := by
  induction bs generalizing w with
  | nil =>
    have hw : selected w = [] := List.eq_nil_of_sublist_nil h
    cases w with
    | nil => exact ⟨[], .nil, .refl _⟩
    | cons a w => simp [selected] at hw
  | cons b bs ih =>
    have hb : b ≠ [] := hn b (by simp)
    have ht : ∀ c ∈ bs, c ≠ [] := fun c hc => hn c (by simp [hc])
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hb
    cases w with
    | nil =>
      obtain ⟨v, hv, _⟩ := ih ht [] (by simp [selected])
      exact ⟨c :: v, .cons (by simp) hv, by simp⟩
    | cons a w =>
      have hp : (selected (a :: w)).Sublist
          ((c :: cs).map some ++ (none :: packed bs)) := by
        simpa [packed, List.append_assoc] using h
      rcases first_payload (c :: cs) a w hp with hs | ⟨hm, hs⟩
      · obtain ⟨v, hv, hw⟩ := ih ht (a :: w) (selected_skip_boundary _ hs)
        exact ⟨c :: v, .cons (by simp) hv, .cons c hw⟩
      · obtain ⟨v, hv, hw⟩ := ih ht w (selected_skip_boundary _ hs)
        exact ⟨a :: v, .cons hm hv, .cons₂ a hw⟩



private theorem choices_embed {α : Type} {bs : List (List α)} {w : List α}
    (h : Chooses bs w) : (selected w).Sublist (packed bs) := by
  induction h with
  | nil => exact .refl _
  | @cons b bs a w ha h ih =>
    have one : [some a].Sublist (b.map some) := by
      exact List.singleton_sublist.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)
    simpa [selected, packed, List.append_assoc] using
      ((one.append_right [none]).append ih)

/-- Monotonicity for complete tails: one old compatible witness extends to one
new compatible witness. This is stronger than extending rows separately. -/
theorem packed_monotone {α : Type} {old new : List (List α)}
    (hn : ∀ b ∈ new, b ≠ []) (h : (packed old).Sublist (packed new))
    {w : List α} (hw : Chooses old w) :
    ∃ v, Chooses new v ∧ w.Sublist v :=
  decode new hn w ((choices_embed hw).trans h)

private theorem choices_append {α : Type} {bs cs : List (List α)} {w v : List α}
    (h : Chooses bs w) (k : Chooses cs v) : Chooses (bs ++ cs) (w ++ v) := by
  induction h with
  | nil => exact k
  | cons ha h ih => exact .cons ha ih

private theorem choices_append_inv {α : Type} {bs cs : List (List α)} {w : List α}
    (h : Chooses (bs ++ cs) w) :
    ∃ u v, w = u ++ v ∧ Chooses bs u ∧ Chooses cs v := by
  induction bs generalizing w with
  | nil => exact ⟨[], w, rfl, .nil, h⟩
  | cons b bs ih =>
    cases h with
    | cons ha ht =>
      obtain ⟨u,v,rfl,hu,hv⟩ := ih ht
      exact ⟨_ :: u, v, rfl, .cons ha hu, hv⟩

private theorem choices_singletons {α : Type} (w : List α) :
    Chooses (w.map fun a => [a]) w := by
  induction w with
  | nil => exact .nil
  | cons a w ih => exact .cons (by simp) ih

private theorem choices_singletons_inv {α : Type} {w v : List α}
    (h : Chooses (w.map fun a => [a]) v) : v = w := by
  induction w generalizing v with
  | nil => cases h; rfl
  | cons a w ih =>
    cases h with
    | cons ha ht =>
      simp only [List.mem_singleton] at ha
      cases ha
      simp [ih ht]

private theorem choices_reverse {α : Type} {bs : List (List α)} {w : List α}
    (h : Chooses bs w) : Chooses bs.reverse w.reverse := by
  induction h with
  | nil => exact .nil
  | cons ha h ih =>
    simpa using choices_append ih (.cons ha .nil)

-- Keep primed letters and primed block ends; erase all punctuation.
def rightProjection : Symbol → Option (Option Letter)
  | .Bp a => some (some a)
  | .Ap => some none
  | _ => none

/-- The raw words may include extraB and all punctuation: only their
primed payload/end-marker projection matters. Thus this applies to theta_i
blocks literally, not merely to encodings with extraB already erased. -/
theorem raw_tail_monotone {oldTail tail : Word} {oldBeta beta : List Letter}
    {oldBlocks blocks : List (List Letter)} {oldWitness : List Letter}
    (ho : oldTail.filterMap rightProjection =
      packed (oldBeta.reverse.map (fun a => [a]) ++ oldBlocks.reverse))
    (hnw : tail.filterMap rightProjection =
      packed (beta.reverse.map (fun a => [a]) ++ blocks.reverse))
    (hn : ∀ b ∈ blocks, b ≠ []) (hs : oldTail.Sublist tail)
    (hw : Chooses oldBlocks oldWitness) :
    ∃ witness, Chooses blocks witness ∧
      (oldWitness ++ oldBeta).Sublist (witness ++ beta) := by
  have hp :
      (packed (oldBeta.reverse.map (fun a => [a]) ++ oldBlocks.reverse)).Sublist
        (packed (beta.reverse.map (fun a => [a]) ++ blocks.reverse)) := by
    simpa only [ho, hnw] using hs.filterMap rightProjection
  have hc := choices_append (choices_singletons oldBeta.reverse) (choices_reverse hw)
  have hn' : ∀ b ∈ beta.reverse.map (fun a => [a]) ++ blocks.reverse, b ≠ [] := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      simp
    · exact hn b (List.mem_reverse.mp hb)
  obtain ⟨v, hv, hsub⟩ := packed_monotone hn' hp hc
  obtain ⟨u, w, rfl, hu, hw'⟩ := choices_append_inv hv
  have he := choices_singletons_inv hu
  subst u
  refine ⟨w.reverse, ?_, ?_⟩
  · simpa using choices_reverse hw'
  · simpa using hsub.reverse



def Good (rows : List (List Letter)) (beta : List Letter)
    (bs : List (List Letter)) : Prop :=
  ∃ witness, Chooses bs witness ∧ ∀ a ∈ rows, a.Sublist (witness ++ beta)

/-- The six-step phase cycle appends the same letter to the last row and to
its common witness. Earlier rows remain subsequences by transitivity. -/
theorem good_append_last {rows : List (List Letter)} {last beta : List Letter}
    {bs : List (List Letter)} (a : Letter) (hg : Good (rows ++ [last]) beta bs) :
    Good (rows ++ [last ++ [a]]) (beta ++ [a]) bs := by
  obtain ⟨w,hw,hr⟩ := hg
  refine ⟨w,hw,?_⟩
  intro r hmem
  rcases List.mem_append.mp hmem with hm | hm
  · exact (hr r (List.mem_append_left _ hm)).trans
      (by simpa [List.append_assoc] using List.sublist_append_left (w ++ beta) [a])
  · have he : r = last ++ [a] := List.mem_singleton.mp hm
    subst r
    simpa [List.append_assoc] using
      (hr last (by simp)).append_right [a]

private theorem choices_length {α : Type} {bs : List (List α)} {w : List α}
    (h : Chooses bs w) : w.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Reading the invariant on the exact reduction target gives a genuine
length-p common supersequence over the original five-letter alphabet. -/
theorem target_sound (i : Instance)
    (hg : Good (markedRows i) [none] (List.replicate i.p letters)) : SCS i := by
  obtain ⟨w,hw,hr⟩ := hg
  have hl : w.length = i.p := by simpa using choices_length hw
  have hb : (w.filterMap id).length ≤ i.p := hl ▸ List.length_filterMap_le id w
  refine ⟨w.filterMap id ++ List.replicate (i.p - (w.filterMap id).length) 0,
    by simp only [List.length_append,List.length_replicate]; omega, ?_⟩
  intro a ha
  have he := hr (a.map some ++ [none]) (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hs : a.Sublist (w.filterMap id) := by
    simpa [List.filterMap_append,List.filterMap_map,Function.comp_def] using he.filterMap id
  exact hs.trans (List.sublist_append_left _ _)


def blockChoices : Block → List Letter
  | none => letters
  | some a => [a]

private theorem block_projection (b : Block) :
    (block b).filterMap rightProjection = (blockChoices b).map some ++ [none] := by
  cases b <;> simp [block,blockChoices,theta,letters,rightProjection]

/-- The literal frame used by the reduction has the required payload
projection, including extraB and all six letters in every full wildcard. -/
theorem frame_projection (rows : List (List Letter)) (beta : List Letter) (bs : List Block) :
    (frame rows beta bs).filterMap rightProjection =
      packed (beta.reverse.map (fun a => [a]) ++ (bs.map blockChoices).reverse) := by
  simp [frame,hr,h,packed,List.filterMap_append,List.filterMap_flatMap,
    List.filterMap_map,List.flatMap_append,← List.map_reverse,List.flatMap_map,
    Function.comp_def,rightProjection,block_projection]

end Soundness

end

/- ================= BLOCK DELIMITERS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace BlockBoundaries

def encode (start stop : Symbol) (bs : List Word) : Word :=
  bs.flatMap fun p => [start] ++ p ++ [stop]

private theorem after_marker_free (a : Symbol) (front rest pre tail : Word)
    (hn : a ∉ front) (he : front ++ rest = pre ++ a :: tail) :
    ∃ q, pre = front ++ q ∧ rest = q ++ a :: tail := by
  induction front generalizing pre with
  | nil => exact ⟨pre,rfl,he⟩
  | cons b front ih =>
    cases pre with
    | nil =>
      have hab : b = a := (List.cons.inj he).1
      subst b
      exact (hn (by simp)).elim
    | cons c pre =>
      have hab : b = c := (List.cons.inj he).1
      subst c
      have ht : front ++ rest = pre ++ a :: tail := (List.cons.inj he).2
      obtain ⟨q,hq,hr⟩ := ih pre (fun hm => hn (List.mem_cons_of_mem _ hm)) ht
      exact ⟨q,by simp [hq],hr⟩

/-- A cut immediately before a start delimiter is a boundary between blocks. -/
theorem prefix_boundary (start stop : Symbol) (bs : List Word)
    (hne : start ≠ stop) (hn : ∀ p ∈ bs, start ∉ p)
    (pre tail : Word) (he : encode start stop bs = pre ++ start :: tail) :
    ∃ left p right, bs = left ++ p :: right ∧ pre = encode start stop left := by
  induction bs generalizing pre with
  | nil =>
    have hlen := congrArg List.length he
    simp [encode] at hlen
    omega
  | cons p bs ih =>
    cases pre with
    | nil => exact ⟨[],p,bs,rfl,rfl⟩
    | cons a pre =>
      have ha : start = a := (List.cons.inj he).1
      subst a
      have ht : (p ++ [stop]) ++ encode start stop bs = pre ++ start :: tail := by
        simpa [encode,List.append_assoc] using (List.cons.inj he).2
      obtain ⟨q,hq,hr⟩ := after_marker_free start (p ++ [stop]) (encode start stop bs)
        pre tail (by simp [hn p (by simp),hne]) ht
      obtain ⟨left,b,right,hbs,hleft⟩ := ih (fun b hb => hn b (by simp [hb])) q hr
      refine ⟨p :: left,b,right,by simp [hbs],?_⟩
      simp [encode,hq,hleft,List.append_assoc]

def reversed (bs : List Word) : List Word := bs.reverse.map List.reverse

private theorem reversed_twice (bs : List Word) : reversed (reversed bs) = bs := by
  simp [reversed,← List.map_reverse,List.map_map,Function.comp_def]

private theorem encode_reverse (start stop : Symbol) (bs : List Word) :
    (encode start stop bs).reverse = encode stop start (reversed bs) := by
  induction bs with
  | nil => rfl
  | cons p bs ih =>
    simpa [encode,reversed,List.flatMap_append,List.append_assoc] using
      congrArg (fun w => w ++ [stop] ++ p.reverse ++ [start]) ih

/-- The dual boundary statement for a cut immediately after a stop delimiter. -/
theorem suffix_boundary (start stop : Symbol) (bs : List Word)
    (hne : start ≠ stop) (hn : ∀ p ∈ bs, stop ∉ p)
    (pre post : Word) (he : encode start stop bs = pre ++ stop :: post) :
    ∃ left p right, bs = left ++ p :: right ∧ post = encode start stop right := by
  have hre : encode stop start (reversed bs) = post.reverse ++ stop :: pre.reverse := by
    simpa [encode_reverse,List.reverse_append,List.append_assoc] using congrArg List.reverse he
  have hnr : ∀ p ∈ reversed bs, stop ∉ p := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    simpa using hn q (List.mem_reverse.mp hq)
  obtain ⟨left,p,right,heq,hpost⟩ := prefix_boundary stop start (reversed bs)
    (Ne.symm hne) hnr post.reverse pre.reverse hre
  have hbs : bs = reversed right ++ p.reverse :: reversed left := by
    have hrev := congrArg reversed heq
    simpa [reversed_twice,reversed,List.reverse_append,List.map_append,
      ← List.map_reverse,List.map_map,Function.comp_def,List.append_assoc] using hrev
  refine ⟨reversed right,p.reverse,reversed left,hbs,?_⟩
  have hr := congrArg List.reverse hpost
  simpa [encode_reverse] using hr

/-- Replacing any complete interval of blocks by another block sequence
preserves the encoding. No condition on how the interval was split into
insertion anchors is needed for this structural fact. -/
theorem replace_blocks (start stop : Symbol) (bs donor : List Word)
    (hne : start ≠ stop)
    (hn : ∀ p ∈ bs, start ∉ p ∧ stop ∉ p)
    (pre middle post : Word)
    (he : encode start stop bs = pre ++ start :: middle ++ stop :: post) :
    ∃ left right, (∀ p ∈ left, p ∈ bs) ∧ (∀ p ∈ right, p ∈ bs) ∧
      pre ++ encode start stop donor ++ post = encode start stop (left ++ donor ++ right) := by
  obtain ⟨left,p,rest,hl,hpre⟩ := prefix_boundary start stop bs hne
    (fun p hp => (hn p hp).1) pre (middle ++ stop :: post)
    (by simpa [List.append_assoc] using he)
  obtain ⟨front,q,right,hr,hpost⟩ := suffix_boundary start stop bs hne
    (fun p hp => (hn p hp).2) (pre ++ start :: middle) post he
  refine ⟨left,right,?_,?_,?_⟩
  · intro p hp
    rw [hl]
    exact List.mem_append_left _ hp
  · intro p hp
    rw [hr]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hp)
  · simp [hpre,hpost,encode,List.flatMap_append,List.append_assoc]


/-- The same block replacement with external prefix/suffix. Only the start
marker must be absent from the prefix and the stop marker from the suffix. -/
theorem replace_context (start stop : Symbol) (bs donor : List Word)
    (hne : start ≠ stop) (hn : ∀ p ∈ bs, start ∉ p ∧ stop ∉ p)
    (lead trail pre middle post : Word)
    (hl : start ∉ lead) (ht : stop ∉ trail)
    (he : lead ++ encode start stop bs ++ trail = pre ++ start :: middle ++ stop :: post) :
    ∃ left right, (∃ rest, bs = left ++ rest) ∧ (∃ front, bs = front ++ right) ∧
      pre ++ encode start stop donor ++ post =
        lead ++ encode start stop (left ++ donor ++ right) ++ trail := by
  obtain ⟨pre',hpre,_⟩ := after_marker_free start lead (encode start stop bs ++ trail)
    pre (middle ++ stop :: post) hl (by simpa [List.append_assoc] using he)
  have hre : trail.reverse ++ ((encode start stop bs).reverse ++ lead.reverse) =
      post.reverse ++ stop :: (pre ++ start :: middle).reverse := by
    simpa [List.reverse_append,List.append_assoc] using congrArg List.reverse he
  obtain ⟨q,hq,_⟩ := after_marker_free stop trail.reverse
    ((encode start stop bs).reverse ++ lead.reverse) post.reverse
    (pre ++ start :: middle).reverse (by simpa using ht) hre
  have hpost : post = q.reverse ++ trail := by
    simpa using congrArg List.reverse hq
  have hcore : encode start stop bs = pre' ++ start :: middle ++ stop :: q.reverse := by
    rw [hpre,hpost] at he
    have he' : lead ++ (encode start stop bs ++ trail) =
        lead ++ ((pre' ++ start :: middle ++ stop :: q.reverse) ++ trail) := by
      simpa [List.append_assoc] using he
    exact List.append_inj_left' (List.append_inj_right he' rfl) rfl
  obtain ⟨left,p,rest,hleft,hle⟩ := prefix_boundary start stop bs hne
    (fun p hp => (hn p hp).1) pre' (middle ++ stop :: q.reverse)
    (by simpa [List.append_assoc] using hcore)
  obtain ⟨front,r,right,hright,hri⟩ := suffix_boundary start stop bs hne
    (fun p hp => (hn p hp).2) (pre' ++ start :: middle) q.reverse hcore
  refine ⟨left,right,⟨p :: rest,hleft⟩,⟨front ++ [r],by simpa [List.append_assoc] using hright⟩,?_⟩
  simp [hpre,hpost,hle,hri,encode,List.flatMap_append,List.append_assoc]


/-- Exact block decomposition at a start marker, with a marker-free trailer. -/
theorem prefix_exact (start stop : Symbol) (bs : List Word) (trail : Word)
    (hne : start ≠ stop) (hn : ∀ p ∈ bs, start ∉ p) (ht : start ∉ trail)
    (pre tail : Word) (he : encode start stop bs ++ trail = pre ++ start :: tail) :
    ∃ left p right, bs = left ++ p :: right ∧ pre = encode start stop left ∧
      tail = p ++ [stop] ++ encode start stop right ++ trail := by
  induction bs generalizing pre with
  | nil =>
    have hm : start ∈ trail := by rw [show trail = pre ++ start :: tail by simpa [encode] using he]; simp
    exact (ht hm).elim
  | cons p bs ih =>
    cases pre with
    | nil =>
      refine ⟨[],p,bs,rfl,rfl,?_⟩
      simpa [encode,List.append_assoc] using (List.cons.inj he).2.symm
    | cons a pre =>
      have ha : start = a := (List.cons.inj he).1
      subst a
      have hrest : (p ++ [stop]) ++ (encode start stop bs ++ trail) = pre ++ start :: tail := by
        simpa [encode,List.append_assoc] using (List.cons.inj he).2
      obtain ⟨q,hq,hqr⟩ := after_marker_free start (p ++ [stop]) (encode start stop bs ++ trail)
        pre tail (by simp [hn p (by simp),hne]) hrest
      obtain ⟨left,r,right,hbs,hpre,htail⟩ := ih (fun q hq => hn q (by simp [hq])) q hqr
      refine ⟨p :: left,r,right,by simp [hbs],?_,htail⟩
      simp [hq,hpre,encode,List.append_assoc]

/-- Every factor from one start marker to a later start marker crosses a stop marker. -/
theorem start_buoy (start stop : Symbol) (bs : List Word) (trail : Word)
    (hne : start ≠ stop) (hn : ∀ p ∈ bs, start ∉ p) (ht : start ∉ trail)
    (pre middle post : Word)
    (he : encode start stop bs ++ trail = pre ++ start :: middle ++ start :: post) :
    stop ∈ middle := by
  obtain ⟨left,p,right,hbs,_,hrest⟩ := prefix_exact start stop bs trail hne hn ht
    pre (middle ++ start :: post) (by simpa [List.append_assoc] using he)
  have hp : start ∉ p := hn p (by rw [hbs]; simp)
  obtain ⟨q,hq,_⟩ := after_marker_free start (p ++ [stop])
    (encode start stop right ++ trail) middle post (by simp [hp,hne])
    (by simpa [List.append_assoc] using hrest.symm)
  simp [hq]

/-- A unique terminal marker has no nonempty suffix after its occurrence. -/
theorem terminal_marker (a : Symbol) (front pre post : Word) (hn : a ∉ front)
    (he : front ++ [a] = pre ++ a :: post) : post = [] := by
  obtain ⟨q,_,hq⟩ := after_marker_free a front [a] pre post hn he
  have hl := congrArg List.length hq
  have hzero : post.length = 0 := by simp only [List.length_cons,List.length_nil,List.length_append] at hl; omega
  exact List.length_eq_zero_iff.mp hzero

end BlockBoundaries

end

/- ================= ALL GENERATED MARKED RIGHT DONORS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol BlockBoundaries
namespace RightStructure

def rawSymbol : Symbol → Bool
  | Bp _ | extraB => true
  | _ => false

def Raw (r : Word) : Prop := (∀ c ∈ r, rawSymbol c = true) ∧ ∃ a, Bp a ∈ r
def Payload (p : Word) : Prop := ∃ r, Raw r ∧ p = r ++ [Ap,spade]
def RotPayload (p : Word) : Prop := ∃ r, Raw r ∧ p = [Cp] ++ r ++ [Ap]
def initial (a : Letter) : Word := [Bp a,Ap,spade]
def Initial (bs : List Word) : Prop := ∃ a tail, bs = initial a :: tail
def terminal (b : Bool) : Word := if b then [natural,diamond] else []
def Inv (w : Word) (b : Bool) : Prop :=
  ∃ bs, Initial bs ∧ (∀ p ∈ bs, Payload p) ∧ w = encode Cp club bs ++ terminal b

theorem initial_payload (a : Letter) : Payload (initial a) := by
  refine ⟨[Bp a],⟨?_,⟨a,by simp⟩⟩,rfl⟩
  simp [rawSymbol]

private theorem payload_markers {p : Word} (h : Payload p) : Cp ∉ p ∧ club ∉ p := by
  obtain ⟨r,hr,rfl⟩ := h
  have hc : Cp ∉ r := by intro hm; have := hr.1 Cp hm; simp [rawSymbol] at this
  have hk : club ∉ r := by intro hm; have := hr.1 club hm; simp [rawSymbol] at this
  simp [hc,hk]

private theorem rot_markers {p : Word} (h : RotPayload p) : club ∉ p ∧ spade ∉ p := by
  obtain ⟨r,hr,rfl⟩ := h
  have hc : club ∉ r := by intro hm; have := hr.1 club hm; simp [rawSymbol] at this
  have hk : spade ∉ r := by intro hm; have := hr.1 spade hm; simp [rawSymbol] at this
  simp [hc,hk]

private theorem prefix_initial {bs left rest donor right : List Word}
    (hi : Initial bs) (he : bs = left ++ rest) (hd : Initial donor) :
    Initial (left ++ donor ++ right) := by
  cases left with
  | nil =>
    obtain ⟨a,tail,rfl⟩ := hd
    exact ⟨a,tail ++ right,rfl⟩
  | cons p left =>
    obtain ⟨a,tail,rfl⟩ := hi
    have hp : initial a = p := (List.cons.inj he).1
    subst p
    exact ⟨a,left ++ donor ++ right,by simp [List.append_assoc]⟩

private theorem payload_concat {P : Word → Prop} {bs left rest front right donor : List Word}
    (hp : ∀ p ∈ bs, P p) (hl : bs = left ++ rest) (hr : bs = front ++ right)
    (hd : ∀ p ∈ donor, P p) : ∀ p ∈ left ++ donor ++ right, P p := by
  intro p hm
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact hp p (by rw [hl]; exact List.mem_append_left _ hm)
  · exact hd p hm
  · exact hp p (by rw [hr]; exact List.mem_append_right _ hm)

/-- A Cp-to-club donor replaces a whole interval of marked blocks. -/
theorem replace_right {x y : Word} {b : Bool} (hx : Inv x b) (hy : Inv y false)
    (pre middle post : Word) (he : x = pre ++ Cp :: middle ++ club :: post) :
    Inv (pre ++ y ++ post) b := by
  obtain ⟨bs,hi,hp,rfl⟩ := hx
  obtain ⟨donor,di,dp,rfl⟩ := hy
  obtain ⟨left,right,⟨rest,hl⟩,⟨front,hr⟩,hout⟩ := replace_context Cp club bs donor
    (by decide) (fun p hm => payload_markers (hp p hm)) [] (terminal b) pre middle post
    (by simp) (by cases b <;> simp [terminal]) (by simpa using he)
  refine ⟨left ++ donor ++ right,prefix_initial hi hl di,
    payload_concat hp hl hr dp,?_⟩
  simpa [terminal] using hout

private theorem rotate (bs : List Word) (hp : ∀ p ∈ bs, Payload p) :
    ∃ qs, (∀ q ∈ qs, RotPayload q) ∧
      [club] ++ encode Cp club bs = encode club spade qs ++ [club] := by
  induction bs with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons p bs ih =>
    obtain ⟨r,hr,rfl⟩ := hp p (by simp)
    obtain ⟨qs,hq,he⟩ := ih (fun p hm => hp p (by simp [hm]))
    refine ⟨([Cp] ++ r ++ [Ap]) :: qs,?_,?_⟩
    · intro q hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨r,hr,rfl⟩
      · exact hq q hm
    · simpa [encode,List.append_assoc] using
        congrArg (fun w => [club,Cp] ++ r ++ [Ap,spade] ++ w) he

private theorem unrotate (qs : List Word) (hq : ∀ q ∈ qs, RotPayload q) :
    ∃ bs, (∀ p ∈ bs, Payload p) ∧
      encode club spade qs ++ [club] = [club] ++ encode Cp club bs := by
  induction qs with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons q qs ih =>
    obtain ⟨r,hr,rfl⟩ := hq q (by simp)
    obtain ⟨bs,hp,he⟩ := ih (fun q hm => hq q (by simp [hm]))
    refine ⟨(r ++ [Ap,spade]) :: bs,?_,?_⟩
    · intro p hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨r,hr,rfl⟩
      · exact hp p hm
    · simpa [encode,List.append_assoc] using
        congrArg (fun w => [club,Cp] ++ r ++ [Ap,spade] ++ w) he

/-- A club-to-spade mask changes a marked interval and leaves the initial
singleton block intact. Empty insertions and boundary anchors are included. -/
theorem replace_mask {x : Word} {b : Bool} (hx : Inv x b) (r : Word) (hr : Raw r)
    (pre middle post : Word) (he : x = pre ++ club :: middle ++ spade :: post) :
    Inv (pre ++ ([club,Cp] ++ r ++ [Ap,spade]) ++ post) b := by
  obtain ⟨bs,⟨a,ps,rfl⟩,hp,hx⟩ := hx
  obtain ⟨qs,hq,hrot⟩ := rotate ps (fun p hm => hp p (List.mem_cons_of_mem _ hm))
  have hview : x = [Cp,Bp a,Ap,spade] ++ encode club spade qs ++ [club] ++ terminal b := by
    have h := congrArg (fun w => [Cp,Bp a,Ap,spade] ++ w ++ terminal b) hrot
    simpa [hx,encode,initial,List.append_assoc] using h
  obtain ⟨left,right,⟨rest,hl⟩,⟨front,hright⟩,hout⟩ := replace_context club spade qs
    [[Cp] ++ r ++ [Ap]] (by decide) (fun q hm => rot_markers (hq q hm))
    [Cp,Bp a,Ap,spade] ([club] ++ terminal b) pre middle post
    (by simp) (by cases b <;> simp [terminal])
    (by simpa [hview,List.append_assoc] using he)
  have hnew : ∀ q ∈ left ++ [[Cp] ++ r ++ [Ap]] ++ right, RotPayload q :=
    payload_concat hq hl hright (by intro q hm; have he := List.mem_singleton.mp hm; subst q; exact ⟨r,hr,rfl⟩)
  obtain ⟨newbs,hbs,heq⟩ := unrotate _ hnew
  refine ⟨initial a :: newbs,⟨a,newbs,rfl⟩,?_,?_⟩
  · intro p hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact initial_payload a
    · exact hbs p hm
  · have h := congrArg (fun w => [Cp,Bp a,Ap,spade] ++ w ++ terminal b) heq
    calc
      pre ++ ([club,Cp] ++ r ++ [Ap,spade]) ++ post =
          [Cp,Bp a,Ap,spade] ++ encode club spade (left ++ [[Cp] ++ r ++ [Ap]] ++ right) ++
            [club] ++ terminal b := by simpa [encode,List.append_assoc] using hout
      _ = encode Cp club (initial a :: newbs) ++ terminal b := by
        simpa [encode,initial,List.append_assoc] using h


private theorem encode_last (start stop : Symbol) (bs : List Word) (hn : bs ≠ []) :
    (encode start stop bs).getLast? = some stop := by
  induction bs with
  | nil => exact (hn rfl).elim
  | cons p bs ih =>
    cases bs with
    | nil =>
      simp only [encode,List.flatMap_cons,List.flatMap_nil,List.append_nil]
      change (([start] ++ p) ++ [stop]).getLast? = some stop
      simp only [List.getLast?_append,List.getLast?_singleton,Option.some_or]
    | cons q bs =>
      change ([start] ++ p ++ [stop] ++ encode start stop (q :: bs)).getLast? = some stop
      simp only [List.getLast?_append,ih (by simp),Option.some_or]

/-- The terminal flag is read directly from the endpoint symbols. -/
theorem inv_ends {w : Word} {b : Bool} (h : Inv w b) :
    FiniteCases.ends w = (some Cp, if b then some diamond else some club) := by
  obtain ⟨bs,⟨a,ps,rfl⟩,_,rfl⟩ := h
  apply Prod.ext
  · simp [FiniteCases.ends,encode,initial]
  · have ht := encode_last Cp club (initial a :: ps) (by simp)
    cases b <;> simp [FiniteCases.ends,terminal,List.getLast?_append,ht]

private theorem payload_no_diamond {p : Word} (hp : Payload p) : diamond ∉ p := by
  obtain ⟨r,hr,rfl⟩ := hp
  have hn : diamond ∉ r := by intro hm; have := hr.1 diamond hm; simp [rawSymbol] at this
  simp [hn]

private theorem encode_no_diamond {bs : List Word} (hp : ∀ p ∈ bs, Payload p) :
    diamond ∉ encode Cp club bs := by
  intro hm
  obtain ⟨p,hp',hm⟩ := List.mem_flatMap.mp hm
  simpa [payload_no_diamond (hp p hp')] using hm

/-- A Cp-to-diamond donor replaces a suffix of blocks through the unique
terminal diamond. It cannot leave an extra suffix after that diamond. -/
theorem replace_end {x y : Word} {b : Bool} (hx : Inv x b) (hy : Inv y true)
    (pre middle post : Word) (he : x = pre ++ Cp :: middle ++ diamond :: post) :
    Inv (pre ++ y ++ post) b := by
  obtain ⟨bs,hi,hp,rfl⟩ := hx
  obtain ⟨donor,di,dp,rfl⟩ := hy
  cases b with
  | false =>
    have hn := encode_no_diamond hp
    have hm : diamond ∈ encode Cp club bs := by
      have hm : diamond ∈ encode Cp club bs ++ terminal false := by rw [he]; simp
      simpa [terminal] using hm
    exact (hn hm).elim
  | true =>
    have hpost : post = [] := terminal_marker diamond (encode Cp club bs ++ [natural])
      (pre ++ Cp :: middle) post (by simp [encode_no_diamond hp])
      (by simpa [terminal,List.append_assoc] using he)
    subst post
    obtain ⟨left,p,right,hbs,hpre,_⟩ := prefix_exact Cp club bs (terminal true)
      (by decide) (fun p hm => (payload_markers (hp p hm)).1) (by simp [terminal])
      pre (middle ++ [diamond]) (by simpa [List.append_assoc] using he)
    refine ⟨left ++ donor,?_,?_,?_⟩
    · simpa using (prefix_initial (right := []) hi hbs di)
    · have hall := payload_concat (front := bs) (right := []) hp hbs (by simp) dp
      simpa using hall
    · simp [hpre,encode,List.flatMap_append,List.append_assoc]

/-- The club delimiter separates every two Cp starts in a right-hand donor. -/
theorem cp_buoy {x : Word} {b : Bool} (hx : Inv x b) (pre middle post : Word)
    (he : x = pre ++ Cp :: middle ++ Cp :: post) : club ∈ middle := by
  obtain ⟨bs,_,hp,rfl⟩ := hx
  exact start_buoy Cp club bs (terminal b) (by decide)
    (fun p hm => (payload_markers (hp p hm)).1) (by cases b <;> simp [terminal])
    pre middle post he

/-- Nonempty anchors inherit the first and last symbols of their donor. -/
theorem anchor_ends (a b : Symbol) (y u z v : Word) (hu : u ≠ []) (hv : v ≠ [])
    (hey : y = u ++ z ++ v) (he : FiniteCases.ends y = (some a,some b)) :
    ∃ us vs, u = a :: us ∧ v = vs ++ [b] := by
  obtain ⟨c,us,rfl⟩ := List.exists_cons_of_ne_nil hu
  have hc : c = a := by simpa [FiniteCases.ends,hey] using congrArg Prod.fst he
  subst c
  have hv' : v.getLast? ≠ none := by simpa using hv
  have hlast : v.getLast? = some b := by
    have ht := congrArg Prod.snd he
    cases he' : v.getLast? with
    | none => exact (hv' he').elim
    | some c =>
      change y.getLast? = some b at ht
      rw [hey] at ht
      simpa only [List.getLast?_append,he',Option.some_or] using ht
  obtain ⟨vs,hvs⟩ := List.getLast?_eq_some_iff.mp hlast
  exact ⟨us,vs,rfl,hvs⟩

/-- A type-1 donor cannot act on a marked right-hand donor: its anchors
would have to cross a club, which it does not contain. -/
theorem no_type_one {x y : Word} {b : Bool} (hx : Inv x b) (hy : Closure seeds y)
    (ey : FiniteCases.ends y = (some Cp,some Cp))
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (hex : x = pre ++ u ++ v ++ post) (hey : y = u ++ z ++ v) : False := by
  obtain ⟨us,vs,rfl,rfl⟩ := anchor_ends Cp Cp y u z v hu hv hey ey
  have hm := cp_buoy hx pre (us ++ vs) post (by simpa [List.append_assoc] using hex)
  obtain ⟨beta,_,he⟩ := TypeOne.generated_one_shape hy ey
  have hn : club ∉ y := by simp [he,hr]
  apply hn
  rw [hey]
  simpa [List.mem_append,or_assoc,or_left_comm,or_comm] using
    (show club ∈ us ∨ club ∈ z ∨ club ∈ vs by
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl hm
      · exact Or.inr (Or.inr hm))


def rightSymbol : Symbol → Bool
  | Cp | Bp _ | Ap | extraB | spade | club | natural | diamond => true
  | _ => false

def rightEnd (p : Option Symbol × Option Symbol) : Bool :=
  p == (some Cp,some club) || p == (some Cp,some diamond)

def rightSeeds : List Word := letters.flatMap fun a =>
  [hr [a] ++ [spade,club,natural,diamond]] ++
  letters.map (fun b => hr [a] ++ [spade,club] ++ hr [b] ++ [spade,club])

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem seed_filter : ∀ w ∈ seeds,
    rightEnd (FiniteCases.ends w) = true → w ∈ rightSeeds := by decide +kernel

private theorem seed_inv {w : Word} (hw : w ∈ seeds)
    (he : rightEnd (FiniteCases.ends w) = true) : ∃ b, Inv w b := by
  have hm := seed_filter w hw he
  obtain ⟨a,_,hm⟩ := List.mem_flatMap.mp hm
  rcases List.mem_append.mp hm with hm | hm
  · have he := List.mem_singleton.mp hm
    subst w
    refine ⟨true,[initial a],⟨a,[],rfl⟩,?_,?_⟩
    · simpa using initial_payload a
    · simp [encode,initial,terminal,hr]
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hm
    refine ⟨false,[initial a,initial b],⟨a,[initial b],rfl⟩,?_,?_⟩
    · intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl
      · exact initial_payload a
      · exact initial_payload b
    · simp [encode,initial,terminal,hr]

private theorem inv_support {w : Word} {b : Bool} (h : Inv w b) : w.all rightSymbol = true := by
  obtain ⟨bs,_,hp,rfl⟩ := h
  apply List.all_eq_true.mpr
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨p,hp',hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨r,hr,rfl⟩ := hp p hp'
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with (rfl | hc | rfl | rfl) | rfl
    all_goals try rfl
    have hb := hr.1 c hc
    cases c <;> simp_all [rawSymbol,rightSymbol]
  · cases b <;> simp [terminal] at hc
    rcases hc with rfl | rfl <;> rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem right_end_cases : ∀ p ∈ seeds.map FiniteCases.ends,
    p.1.any rightSymbol = true → p.2.any rightSymbol = true →
    p = (some Cp,some Cp) ∨ p = (some Cp,some club) ∨
      p = (some Cp,some diamond) ∨ p = (some club,some spade) := by decide +kernel

def maskSeeds : List Word := List.ofFn fun i : Fin 6 =>
  [club,Cp] ++ theta (i.val+1) ++ [Ap,spade]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem mask_filter : ∀ w ∈ FiniteCases.small,
    FiniteCases.ends w = (some club,some spade) → w ∈ maskSeeds := by decide +kernel

private theorem mask_shape {w : Word} (h : Closure seeds w)
    (he : FiniteCases.ends w = (some club,some spade)) :
    ∃ i : Fin 6, w = [club,Cp] ++ theta (i.val+1) ++ [Ap,spade] := by
  have hs := FiniteCases.generated_small h (by simp [he,FiniteCases.smallEnd])
  have hm := mask_filter w hs he
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  exact ⟨i,hi.symm⟩

private theorem theta_raw (i : Fin 6) : Raw (theta (i.val+1)) := by
  constructor
  · intro c hc
    simp only [theta,List.mem_cons,List.mem_map] at hc
    rcases hc with rfl | ⟨a,_,rfl⟩ <;> rfl
  · refine ⟨none,?_⟩
    change Bp none ∈ extraB :: Bp none :: _
    simp

private theorem endpoint_splice (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ []) :
    FiniteCases.ends (pre ++ u ++ z ++ v ++ post) = FiniteCases.ends (pre ++ u ++ v ++ post) := by
  apply Prod.ext
  · cases pre <;> cases u <;> simp_all [FiniteCases.ends]
  · have hv' : v.getLast? ≠ none := by simpa using hv
    cases hp : post.getLast? with
    | some a => simp [FiniteCases.ends,List.getLast?_append,hp]
    | none =>
      cases ht : v.getLast? with
      | none => exact (hv' ht).elim
      | some a => simp [FiniteCases.ends,List.getLast?_append,hp,ht]

/-- Unconditional classification of every generated marked right-hand donor.
Payloads are allowed to be more general than theta-prefixes; this weaker
invariant is sufficient for soundness and is preserved by all donor cases. -/
theorem generated_right {w : Word} (h : Closure seeds w)
    (he : rightEnd (FiniteCases.ends w) = true) : ∃ b, Inv w b := by
  induction h with
  | seed hw => exact seed_inv hw he
  | @insert x y pre post u v z hx hy hu hv ex ey ihx ihy =>
    have hxe : rightEnd (FiniteCases.ends x) = true := by
      rw [ex]
      simpa only [endpoint_splice _ _ _ _ _ hu hv] using he
    obtain ⟨b,hxi⟩ := ihx hxe
    have has := AlphabetInvariant.donor_allowed rightSymbol pre u v post z hu hv
      (by simpa [ex] using inv_support hxi)
    have hcases := right_end_cases (FiniteCases.ends y) (FiniteCases.closure_ends hy)
      (by simpa [AlphabetInvariant.endAllowed,FiniteCases.ends,ey] using has.1)
      (by simpa [AlphabetInvariant.endAllowed,FiniteCases.ends,ey] using has.2)
    rcases hcases with he | he | he | he
    · exact (no_type_one hxi hy he pre u v post z hu hv ex ey).elim
    · obtain ⟨c,hyi⟩ := ihy (by simp [rightEnd,he])
      have hc := inv_ends hyi
      have hcf : c = false := by cases c <;> simp_all
      subst c
      obtain ⟨us,vs,rfl,rfl⟩ := anchor_ends Cp club y u z v hu hv ey he
      refine ⟨b,?_⟩
      have hnew := replace_right hxi hyi pre (us ++ vs) post
        (by simpa [List.append_assoc] using ex)
      simpa [ey,List.append_assoc] using hnew
    · obtain ⟨c,hyi⟩ := ihy (by simp [rightEnd,he])
      have hc := inv_ends hyi
      have hct : c = true := by cases c <;> simp_all
      subst c
      obtain ⟨us,vs,rfl,rfl⟩ := anchor_ends Cp diamond y u z v hu hv ey he
      refine ⟨b,?_⟩
      have hnew := replace_end hxi hyi pre (us ++ vs) post
        (by simpa [List.append_assoc] using ex)
      simpa [ey,List.append_assoc] using hnew
    · obtain ⟨i,hmask⟩ := mask_shape hy he
      obtain ⟨us,vs,rfl,rfl⟩ := anchor_ends club spade y u z v hu hv ey he
      refine ⟨b,?_⟩
      have hnew := replace_mask hxi (theta (i.val+1)) (theta_raw i) pre (us ++ vs) post
        (by simpa [List.append_assoc] using ex)
      rw [← hmask] at hnew
      simpa [ey,List.append_assoc] using hnew

end RightStructure

end

/- ================= LOCALIZING PHASE INSERTIONS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases
namespace Localization

private theorem longer_prefix (a b c d : Word) (he : a ++ b = c ++ d)
    (hl : c.length ≤ a.length) : ∃ q, a = c ++ q := by
  rcases List.append_eq_append_iff.mp he with ⟨q,hc,_⟩ | ⟨q,ha,_⟩
  · have hlen := congrArg List.length hc
    have hq : q.length = 0 := by simp only [List.length_append] at hlen; omega
    have hq' : q = [] := List.length_eq_zero_iff.mp hq
    exact ⟨[],by simpa [hq'] using hc.symm⟩
  · exact ⟨q,ha⟩

/-- If the insertion factor lies inside a designated window, the insertion
is one of the finite insertions enumerated on that window. -/
theorem inside_window (lead window trail pre u v post z : Word)
    (he : lead ++ window ++ trail = pre ++ u ++ v ++ post)
    (hl : lead.length ≤ pre.length) (hr : trail.length ≤ post.length)
    (hu : u ≠ []) (hv : v ≠ []) :
    ∃ result, result ∈ inserts window (u ++ z ++ v) ∧
      pre ++ u ++ z ++ v ++ post = lead ++ result ++ trail := by
  obtain ⟨left,hleft⟩ := longer_prefix pre (u ++ v ++ post) lead (window ++ trail)
    (by simpa [List.append_assoc] using he.symm) hl
  have hre : post.reverse ++ (v.reverse ++ u.reverse ++ pre.reverse) =
      trail.reverse ++ (window.reverse ++ lead.reverse) := by
    simpa [List.reverse_append,List.append_assoc] using congrArg List.reverse he.symm
  obtain ⟨right,hright⟩ := longer_prefix post.reverse (v.reverse ++ u.reverse ++ pre.reverse)
    trail.reverse (window.reverse ++ lead.reverse) hre (by simpa using hr)
  have hpost : post = right.reverse ++ trail := by simpa using congrArg List.reverse hright
  have hw : window = left ++ u ++ v ++ right.reverse := by
    rw [hleft,hpost] at he
    have he' : lead ++ (window ++ trail) = lead ++ ((left ++ u ++ v ++ right.reverse) ++ trail) := by
      simpa [List.append_assoc] using he
    exact List.append_inj_left' (List.append_inj_right he' rfl) rfl
  refine ⟨left ++ u ++ z ++ v ++ right.reverse,?_,?_⟩
  · rw [hw]
    exact insert_mem _ _ _ _ _ hu hv
  · simp [hleft,hpost,List.append_assoc]

private theorem marker_index (lead tail : Word) (hn : flat ∉ lead) :
    (lead ++ flat :: tail).idxOf flat = lead.length := by
  simp [List.idxOf_append,hn]

private theorem factor_index (pre f post : Word) (hn : flat ∉ pre) (hm : flat ∈ f) :
    (pre ++ f ++ post).idxOf flat = pre.length + f.idxOf flat := by
  simp [List.idxOf_append,hn,hm,List.mem_append,Nat.add_comm]

/-- A donor with at most |left| symbols before its unique flat and at most
|right| after it can only modify this bounded junction window. -/
theorem centered_window (lead left right trail pre u v post z : Word)
    (he : lead ++ (left ++ flat :: right) ++ trail = pre ++ u ++ v ++ post)
    (hll : flat ∉ lead) (hl : flat ∉ left) (hr : flat ∉ right) (hrr : flat ∉ trail)
    (hpre : flat ∉ pre) (hpost : flat ∉ post)
    (hm : flat ∈ u ++ v)
    (bl : (u ++ v).idxOf flat ≤ left.length)
    (br : (u ++ v).reverse.idxOf flat ≤ right.length)
    (hu : u ≠ []) (hv : v ≠ []) :
    ∃ result, result ∈ inserts (left ++ flat :: right) (u ++ z ++ v) ∧
      pre ++ u ++ z ++ v ++ post = lead ++ result ++ trail := by
  have hi : lead.length + left.length = pre.length + (u ++ v).idxOf flat := by
    have h := congrArg (fun w : Word => w.idxOf flat) he
    have hleft : (lead ++ (left ++ flat :: right) ++ trail).idxOf flat = lead.length + left.length := by
      simpa [List.append_assoc] using marker_index (lead ++ left) (right ++ trail) (by simp [hll,hl])
    have hright : (pre ++ u ++ v ++ post).idxOf flat = pre.length + (u ++ v).idxOf flat := by
      simpa [List.append_assoc] using factor_index pre (u ++ v) post hpre hm
    simpa only [hleft,hright] using h
  have hj : trail.length + right.length = post.length + (u ++ v).reverse.idxOf flat := by
    have h := congrArg (fun w : Word => w.reverse.idxOf flat) he
    have hleft : (lead ++ (left ++ flat :: right) ++ trail).reverse.idxOf flat = trail.length + right.length := by
      simpa [List.reverse_append,List.append_assoc] using
        marker_index (trail.reverse ++ right.reverse) (left.reverse ++ lead.reverse) (by simp [hrr,hr])
    have hright : (pre ++ u ++ v ++ post).reverse.idxOf flat = post.length + (u ++ v).reverse.idxOf flat := by
      simpa [List.reverse_append,List.append_assoc] using
        factor_index post.reverse (u ++ v).reverse pre.reverse (by simpa using hpost) (List.mem_reverse.mpr hm)
    simpa only [hleft,hright] using h
  exact inside_window lead (left ++ flat :: right) trail pre u v post z he
    (by omega) (by omega) hu hv

end Localization

end

/- ================= DECODING RAW BLOCKS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol BlockBoundaries Soundness
namespace RightStructure

def payloadLetters (p : Word) : List Letter := p.filterMap fun s =>
  match s with | Bp a => some a | _ => none
private theorem raw_projection {r : Word} (hr : ∀ c ∈ r, rawSymbol c = true) :
    r.filterMap rightProjection = (payloadLetters r).map some := by
  induction r with
  | nil => rfl
  | cons c r ih =>
    have hc := hr c (by simp)
    have hrest := ih (fun d hd => hr d (by simp [hd]))
    cases c <;> simp_all [rawSymbol,payloadLetters,rightProjection]
theorem payload_projection {p : Word} (hp : Payload p) :
    p.filterMap rightProjection = (payloadLetters p).map some ++ [none] := by
  obtain ⟨r,hr,rfl⟩ := hp
  simp [List.filterMap_append,rightProjection,payloadLetters] at *
  exact raw_projection hr.1
theorem payload_letters_nonempty {p : Word} (hp : Payload p) : payloadLetters p ≠ [] := by
  obtain ⟨r,hr,rfl⟩ := hp
  obtain ⟨a,ha⟩ := hr.2
  have hm : a ∈ payloadLetters (r ++ [Ap,spade]) := by
    exact List.mem_filterMap.mpr ⟨Bp a,List.mem_append_left _ ha,rfl⟩
  intro he
  simpa [he] using hm
/-- All generated marked donors decode to nonempty blocks and start with a singleton. -/
theorem inv_projection {w : Word} {flag : Bool} (hw : Inv w flag) :
    ∃ a bs, (∀ b ∈ bs, b ≠ []) ∧
      w.filterMap rightProjection = packed ([a] :: bs) := by
  obtain ⟨ps,⟨a,ps',rfl⟩,hp,rfl⟩ := hw
  refine ⟨a,ps'.map payloadLetters,?_,?_⟩
  · intro b hb
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hb
    exact payload_letters_nonempty (hp p (by simp [hp']))
  · have henc : (encode Cp club ps').filterMap rightProjection = packed (ps'.map payloadLetters) := by
      unfold encode packed
      rw [List.filterMap_flatMap,List.flatMap_map]
      simp only [List.flatMap_def]
      apply congrArg List.flatten
      apply List.map_congr_left
      intro p hm
      simp [List.filterMap_append,rightProjection,payload_projection (hp p (by simp [hm]))]
    cases flag <;>
      simp [encode,initial,List.filterMap_append,rightProjection,terminal,packed,
        List.filterMap_flatMap,List.flatMap_map] at henc ⊢
    all_goals exact henc
end RightStructure

end

/- ================= ROW PROJECTION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace Soundness
/-- Split at explicit row terminators; this also recovers empty rows. -/
def unpack {α : Type} : List (Option α) → List (List α)
  | [] => []
  | none :: s => [] :: unpack s
  | some a :: s => match unpack s with
      | [] => [[a]] | b :: bs => (a :: b) :: bs
private theorem unpack_row {α : Type} (r : List α) (s : List (Option α)) :
    unpack (r.map some ++ none :: s) = r :: unpack s := by
  induction r with
  | nil => rfl
  | cons a r ih => simp [unpack,ih]
theorem unpack_packed {α : Type} (rows : List (List α)) : unpack (packed rows) = rows := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    have he := unpack_row r (packed rows)
    rw [ih] at he
    simpa only [packed,List.flatMap_cons,List.append_assoc,List.singleton_append] using he
theorem packed_injective {α : Type} {rows rows' : List (List α)}
    (he : packed rows = packed rows') : rows = rows' := by
  simpa only [unpack_packed] using congrArg unpack he

def rowToken : Symbol → Option (Option Letter)
  | B a => some (some a) | sharp => some none | _ => none
theorem row_projection (rows : List (List Letter)) :
    (rows.flatMap fun a => h a ++ [sharp,dollar]).filterMap rowToken = packed rows := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    have hrow : (h r).filterMap rowToken = r.map some := by
      induction r with
      | nil => rfl
      | cons a r ih => simpa [h,List.filterMap_append,rowToken] using ih
    simpa [packed,List.filterMap_append,hrow,rowToken,List.append_assoc] using
      congrArg (fun s => r.map some ++ none :: s) ih
theorem frame_rows (rows : List (List Letter)) (beta : List Letter) (bs : List Block) :
    (frame rows beta bs).filterMap rowToken = packed rows := by
  have hb (b : Block) : (block b).filterMap rowToken = [] := by cases b <;> rfl
  have hbeta : (hr beta).filterMap rowToken = [] := by
    simp [hr,List.filterMap_flatMap,rowToken]
  have hbs : (bs.reverse.flatMap fun b => [spade,club] ++ block b).filterMap rowToken = [] := by
    simp [List.filterMap_flatMap,List.filterMap_append,rowToken,hb]
  simp only [frame,List.filterMap_append,row_projection,hbeta,hbs]
  simp [rowToken]
end Soundness

end

/- ================= SKIPPING MARKER-FREE PREFIXES ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace Soundness
/-- An embedding starting at a block marker skips any marker-free prefix. -/
theorem skip_marker_free {α : Type} (a : α) (lead rest tail : List α)
    (hn : a ∉ lead) (hs : (a :: rest).Sublist (lead ++ tail)) :
    (a :: rest).Sublist tail := by
  induction lead with
  | nil => exact hs
  | cons b lead ih =>
    cases hs with
    | cons _ hs => exact ih (fun hm => hn (by simp [hm])) hs
    | cons₂ _ hs => exact (hn (by simp)).elim

end Soundness

end

/- ================= PHASE DEFINITIONS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases LocalSyntax
namespace PhaseCases
set_option Elab.async false
inductive Phase where
  | ready | leftA | leftA_rightAp | leftAB (a : Letter) | bothB (a : Letter) | leftABC (a : Letter)
  deriving DecidableEq

def phaseLeft : Phase → Word
  | .ready => []
  | .leftA | .leftA_rightAp => [A]
  | .leftAB a | .bothB a => [A,B a]
  | .leftABC a => [A,B a,C]
def phaseRight : Phase → Word
  | .ready | .leftA => []
  | .leftA_rightAp | .leftAB _ => [Ap]
  | .bothB a | .leftABC a => [Bp a,Ap]
def window (p : Phase) (c d : Letter) : Word :=
  h [c] ++ phaseLeft p ++ [sharp,flat] ++ phaseRight p ++ hr [d]
def advance (p : Phase) (c d e : Letter) : Word :=
  match p with
  | .ready => window .leftA c d
  | .leftA => window .leftA_rightAp c d
  | .leftA_rightAp => window (.leftAB e) c d
  | .leftAB a => window (.bothB a) c d
  | .bothB a => window (.leftABC a) c d
  | .leftABC a => h [c,a] ++ [sharp,flat] ++ hr [d,a]
def factors (y : Word) : List Word :=
  (cuts y).flatMap fun (u,r) => (cuts r).map fun (_,v) => u ++ v

theorem factor_mem (u z v : Word) : u ++ v ∈ factors (u ++ z ++ v) := by
  apply List.mem_flatMap.mpr
  refine ⟨(u,z ++ v),?_,?_⟩
  · simpa [List.append_assoc] using cut_mem u (z ++ v)
  · exact List.mem_map.mpr ⟨(z,v),cut_mem z v,rfl⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem factor_bounds : ∀ e ∈ letters, ∀ y ∈ Completion.donors e,
    ∀ f ∈ factors y, flat ∈ f → f.idxOf flat ≤ 4 ∧ f.reverse.idxOf flat ≤ 3 := by
  decide +kernel
end PhaseCases

end

/- ================= SYMBOLIC PHASE CASES ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases LocalSyntax
namespace PhaseCases
set_option Elab.async false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- Exhaust the six phase shapes and six donors. Letters remain arbitrary;
only the finitely many anchor cuts are enumerated. -/
theorem window_result (p : Phase) (c d e : Letter) {y result : Word}
    (hy : y ∈ Completion.donors e) (hr : result ∈ inserts (window p c d) y) :
    result = window p c d ∨ result = advance p c d e := by
  simp only [Completion.donors,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals cases p <;>
    simp [inserts,cuts,List.range_succ,window,advance,phaseLeft,phaseRight,h,
      SupersequenceReduction.hr] at hr ⊢ <;> grind
end PhaseCases

end

/- ================= PHASE LOCALIZATION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases LocalSyntax
namespace PhaseCases
private theorem donor_ranks (e : Letter) {y : Word} (hy : y ∈ Completion.donors e) :
    ∃ a b, ends y = (some a,some b) ∧ rank a = 1 ∧ rank b = 3 := by
  simp only [Completion.donors,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_,_,rfl,rfl,rfl⟩

theorem outside_flat_free {x y : Word} (hx : Closure seeds x)
    (e : Letter) (hy : y ∈ Completion.donors e)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) : flat ∉ pre ∧ flat ∉ post := by
  obtain ⟨a,b,he,ha,hb⟩ := donor_ranks e hy
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends a b y u z v hu hv ey he
  have ho := closure_ordered hx
  rw [ex] at ho
  constructor
  · intro hm
    have hp : (pre ++ ((a :: us) ++ (vs ++ [b]) ++ post)).Pairwise ordered := by
      simpa [List.append_assoc] using ho
    have hr := (List.pairwise_append.mp hp).2.2 flat hm a (by simp)
    unfold ordered at hr
    rw [ha] at hr
    simp [rank] at hr
  · intro hm
    have hr := (List.pairwise_append.mp ho).2.2 b (by simp) flat hm
    unfold ordered at hr
    rw [hb] at hr
    simp [rank] at hr

/-- Localization makes the finite phase calculation apply in arbitrary contexts. -/
theorem phase_insert {x y : Word} (hx : Closure seeds x)
    (p : Phase) (c d e : Letter) (hy : y ∈ Completion.donors e)
    (lead trail : Word) (hframe : x = lead ++ window p c d ++ trail)
    (hlead : flat ∉ lead) (htrail : flat ∉ trail)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    pre ++ u ++ z ++ v ++ post = x ∨
      pre ++ u ++ z ++ v ++ post = lead ++ advance p c d e ++ trail := by
  obtain ⟨hpre,hpost⟩ := outside_flat_free hx e hy pre u v post z hu hv ex ey
  have hm : flat ∈ u ++ v := by
    have hm : flat ∈ x := by rw [hframe]; simp [window]
    simpa [ex,List.mem_append,hpre,hpost] using hm
  have hb := factor_bounds e (Completion.letter_mem e) y hy (u ++ v)
    (by rw [ey]; exact factor_mem u z v) hm
  let l := h [c] ++ phaseLeft p ++ [sharp]
  let r := phaseRight p ++ hr [d]
  have hl : flat ∉ l := by cases p <;> simp [l,h,phaseLeft]
  have hRight : flat ∉ r := by cases p <;> simp [r,hr,phaseRight]
  have hll : 4 ≤ l.length := by cases p <;> simp [l,h,phaseLeft]
  have hrr : 3 ≤ r.length := by cases p <;> simp [r,hr,phaseRight]
  obtain ⟨result,hresult,hout⟩ := Localization.centered_window lead l r trail pre u v post z
    (by simpa [hframe,window,l,r,List.append_assoc] using ex)
    hlead hl hRight htrail hpre hpost hm (by omega) (by omega) hu hv
  have hresult' : result ∈ inserts (window p c d) y := by
    simpa [window,l,r,ey,List.append_assoc] using hresult
  rcases window_result p c d e hy hresult' with h | h
  · left; simpa [h,hframe] using hout
  · right; simpa [h] using hout
end PhaseCases

end

/- ================= PHASE SEMANTICS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases LocalSyntax
namespace PhaseCases

def body (lead : Word) (alpha beta : List Letter) (p : Phase) (tail : Word) : Word :=
  lead ++ h alpha ++ phaseLeft p ++ [sharp,flat] ++ phaseRight p ++ hr beta ++ tail
def nextPhase : Phase → Letter → Phase
  | .ready, _ => .leftA
  | .leftA, _ => .leftA_rightAp
  | .leftA_rightAp, e => .leftAB e
  | .leftAB a, _ => .bothB a
  | .bothB a, _ => .leftABC a
  | .leftABC _, _ => .ready
def nextWord (p : Phase) (w : List Letter) : List Letter :=
  match p with | .leftABC a => w ++ [a] | _ => w

theorem nextWord_nonempty (p : Phase) {w : List Letter} (hw : w ≠ []) : nextWord p w ≠ [] := by
  cases p <;> simp_all [nextWord]

/-- Completing the cycle appends the same letter to the last row and its
common witness. Earlier rows remain subsequences of that one witness. -/
theorem next_good (p : Phase) {rows : List (List Letter)} {alpha beta : List Letter}
    {blocks : List (List Letter)} (hg : Soundness.Good (rows ++ [alpha]) beta blocks) :
    Soundness.Good (rows ++ [nextWord p alpha]) (nextWord p beta) blocks := by
  cases p <;> simp only [nextWord]
  all_goals first | exact hg | exact Soundness.good_append_last _ hg

private theorem split_last {w : List Letter} (hw : w ≠ []) : ∃ a c, w = a ++ [c] := by
  have hn : w.getLast? ≠ none := by simpa using hw
  cases he : w.getLast? with
  | none => exact (hn he).elim
  | some c => obtain ⟨a,ha⟩ := List.getLast?_eq_some_iff.mp he; exact ⟨a,c,ha⟩

private theorem advance_body (lead tail : Word) (a b : List Letter) (c d e : Letter) (p : Phase) :
    (lead ++ h a) ++ advance p c d e ++ (hr b ++ tail) =
      body lead (nextWord p (a ++ [c])) (nextWord p (b ++ [d])) (nextPhase p e) tail := by
  cases p <;> simp [advance,window,body,nextWord,nextPhase,h,hr,List.reverse_append,
    List.flatMap_append,List.append_assoc,phaseLeft,phaseRight]

/-- Complete semantic phase preservation for arbitrary-length words. -/
theorem phase_preserves {x y : Word} (hx : Closure seeds x)
    (lead tail : Word) (alpha beta : List Letter) (p : Phase) (e : Letter)
    (rows : List (List Letter)) (blocks : List (List Letter))
    (ha : alpha ≠ []) (hb : beta ≠ [])
    (hp : flat ∉ lead) (ht : flat ∉ tail)
    (hf : x = body lead alpha beta p tail)
    (hg : Soundness.Good (rows ++ [alpha]) beta blocks)
    (hy : y ∈ Completion.donors e)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    ∃ p' alpha' beta', alpha' ≠ [] ∧ beta' ≠ [] ∧
      pre ++ u ++ z ++ v ++ post = body lead alpha' beta' p' tail ∧
      Soundness.Good (rows ++ [alpha']) beta' blocks := by
  obtain ⟨a,c,rfl⟩ := split_last ha
  obtain ⟨b,d,rfl⟩ := split_last hb
  have hw : x = (lead ++ h a) ++ window p c d ++ (hr b ++ tail) := by
    simpa [body,window,h,hr,List.reverse_append,List.flatMap_append,List.append_assoc] using hf
  have hl : flat ∉ lead ++ h a := by
    simp only [List.mem_append,not_or]
    exact ⟨hp,by simp [h]⟩
  have hr' : flat ∉ hr b ++ tail := by
    simp only [List.mem_append,not_or]
    exact ⟨by simp [hr],ht⟩
  rcases phase_insert hx p c d e hy (lead ++ h a) (hr b ++ tail)
      hw hl hr' pre u v post z hu hv ex ey with he | he
  · exact ⟨p,a ++ [c],b ++ [d],ha,hb,he.trans hf,hg⟩
  · exact ⟨nextPhase p e,nextWord p (a ++ [c]),nextWord p (b ++ [d]),
      nextWord_nonempty p ha,nextWord_nonempty p hb,
      he.trans (advance_body lead tail a b c d e p),next_good p hg⟩
end PhaseCases

end

/- ================= COMPLETED JUNCTION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases LocalSyntax
namespace PhaseCases
set_option Elab.async false
def finishedWindow (c d : Letter) : Word := h [c] ++ [sharp,dollar,flat] ++ hr [d]
def finishedCert (c : Letter) : Bool := letters.all fun d => letters.all fun e =>
  (Completion.donors e).all fun y => (inserts (finishedWindow c d) y).isEmpty
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem finished_check : (letters.all finishedCert) = true := by decide +kernel

/-- After the final dollar has been inserted, no short phase donor applies. -/
theorem finished_no_phase {x y : Word} (hx : Closure seeds x)
    (c d e : Letter) (hy : y ∈ Completion.donors e)
    (lead trail : Word) (hframe : x = lead ++ finishedWindow c d ++ trail)
    (hlead : flat ∉ lead) (htrail : flat ∉ trail)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) : False := by
  obtain ⟨hpre,hpost⟩ := outside_flat_free hx e hy pre u v post z hu hv ex ey
  have hm : flat ∈ u ++ v := by
    have hm : flat ∈ x := by rw [hframe]; simp [finishedWindow]
    simpa [ex,List.mem_append,hpre,hpost] using hm
  have hb := factor_bounds e (Completion.letter_mem e) y hy (u ++ v)
    (by rw [ey]; exact factor_mem u z v) hm
  obtain ⟨result,hresult,_⟩ := Localization.centered_window lead (h [c] ++ [sharp,dollar])
    (hr [d]) trail pre u v post z
    (by simpa [hframe,finishedWindow,List.append_assoc] using ex)
    hlead (by simp [h]) (by simp [hr]) htrail hpre hpost hm
    (by simpa [h] using (show (u ++ v).idxOf flat ≤ 5 by omega))
    (by simpa [hr] using hb.2) hu hv
  have hresult' : result ∈ inserts (finishedWindow c d) y := by
    simpa [finishedWindow,ey,List.append_assoc] using hresult
  have hc := finished_check
  simp only [List.all_eq_true,finishedCert] at hc
  have hc := hc c (Completion.letter_mem c)
  simp only [List.all_eq_true,List.isEmpty_iff] at hc
  have hn := hc d (Completion.letter_mem d) e (Completion.letter_mem e) y hy
  simpa [hn] using hresult'
end PhaseCases

end

/- ================= SYMBOLIC BRIDGE CASES ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases LocalSyntax
namespace PhaseCases
set_option Elab.async false
set_option grind.warning false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
-- `none` denotes a completed junction with the trailing dollar.
def junctionLeft : Option Phase → Word
  | none => [] | some p => phaseLeft p
def junctionRight : Option Phase → Word
  | none => [] | some p => phaseRight p
def punctuation : Option Phase → Word
  | none => [sharp,dollar] | some _ => [sharp]
def paddedWindow (q : Symbol) (j : Option Phase) (c d : Letter) : Word :=
  [q] ++ h [c] ++ junctionLeft j ++ punctuation j ++ [flat] ++ junctionRight j ++ hr [d]
def bridge (a b : Letter) : Word := h [a] ++ [sharp,dollar,flat] ++ hr [b]

/-- Symbolic case analysis: letters are arbitrary and every anchor cut is checked. -/
theorem bridge_result (j : Option Phase) (c d a b : Letter) (q : Symbol)
    (hq : q ∈ [C,dollar]) {w : Word}
    (hw : w ∈ inserts (paddedWindow q j c d) (bridge a b)) :
    w = paddedWindow q j c d ∨ j = some Phase.ready ∧ w = paddedWindow q none c d := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl
  all_goals cases j with
  | none =>
    simp [paddedWindow,junctionLeft,junctionRight,punctuation,bridge,h,hr,
      inserts,cuts,List.range_succ] at hw ⊢
    grind
  | some p =>
    cases p <;>
      simp [paddedWindow,junctionLeft,junctionRight,punctuation,phaseLeft,phaseRight,bridge,h,hr,
        inserts,cuts,List.range_succ] at hw ⊢ <;> grind

theorem bridge_bounds : ∀ a ∈ letters, ∀ b ∈ letters, ∀ f ∈ factors (bridge a b),
    flat ∈ f → f.idxOf flat ≤ 5 ∧ f.reverse.idxOf flat ≤ 3 := by decide +kernel
end PhaseCases

end

/- ================= BRIDGE LOCALIZATION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases LocalSyntax
namespace PhaseCases
/-- The bridge can only add the dollar at a completed phase. Padding covers
the maximal anchor length even when the last row has just one letter. -/
theorem bridge_insert {x y : Word} (hx : Closure seeds x)
    (j : Option Phase) (c d a b : Letter) (q : Symbol) (hq : q ∈ [C,dollar])
    (lead trail : Word) (hframe : x = lead ++ paddedWindow q j c d ++ trail)
    (hlead : flat ∉ lead) (htrail : flat ∉ trail) (hy : y = bridge a b)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    pre ++ u ++ z ++ v ++ post = x ∨
      j = some Phase.ready ∧
      pre ++ u ++ z ++ v ++ post = lead ++ paddedWindow q none c d ++ trail := by
  have he : ends y = (some A,some Ap) := by simp [hy,bridge,h,hr,ends]
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends A Ap y u z v hu hv ey he
  have ho := closure_ordered hx
  rw [ex] at ho
  have hpre : flat ∉ pre := by
    intro hm
    have hp : (pre ++ ((A :: us) ++ (vs ++ [Ap]) ++ post)).Pairwise ordered := by
      simpa [List.append_assoc] using ho
    have ht := (List.pairwise_append.mp hp).2.2 flat hm A (by simp)
    simp [ordered,rank] at ht
  have hpost : flat ∉ post := by
    intro hm
    have ht := (List.pairwise_append.mp ho).2.2 Ap (by simp) flat hm
    simp [ordered,rank] at ht
  have hm : flat ∈ (A :: us) ++ (vs ++ [Ap]) := by
    have hm : flat ∈ x := by rw [hframe]; simp [paddedWindow]
    simpa [ex,List.mem_append,hpre,hpost] using hm
  have hf : (A :: us) ++ (vs ++ [Ap]) ∈ factors (bridge a b) := by
    rw [← hy,ey]; exact factor_mem _ _ _
  have hb := bridge_bounds a (Completion.letter_mem a) b (Completion.letter_mem b) _ hf hm
  let l := [q] ++ h [c] ++ junctionLeft j ++ punctuation j
  let r := junctionRight j ++ hr [d]
  have hqflat : q ≠ flat := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl <;> decide
  have hl : flat ∉ l := by
    cases j with
    | none => simp [l,junctionLeft,punctuation,h,hqflat,Ne.symm hqflat]
    | some p => cases p <;> simp [l,junctionLeft,punctuation,phaseLeft,h,hqflat,Ne.symm hqflat]
  have hr' : flat ∉ r := by
    cases j with
    | none => simp [r,junctionRight,hr]
    | some p => cases p <;> simp [r,junctionRight,phaseRight,hr]
  have hll : 5 ≤ l.length := by
    cases j with
    | none => simp [l,junctionLeft,punctuation,h]
    | some p => cases p <;> simp [l,junctionLeft,punctuation,phaseLeft,h]
  have hrr : 3 ≤ r.length := by
    cases j with
    | none => simp [r,junctionRight,hr]
    | some p => cases p <;> simp [r,junctionRight,phaseRight,hr]
  obtain ⟨result,hresult,hout⟩ := Localization.centered_window lead l r trail pre
    (A :: us) (vs ++ [Ap]) post z
    (by simpa [hframe,paddedWindow,l,r,List.append_assoc] using ex)
    hlead hl hr' htrail hpre hpost hm (by omega) (by omega) hu hv
  have hresult' : result ∈ inserts (paddedWindow q j c d) (bridge a b) := by
    have hd : (A :: us) ++ z ++ (vs ++ [Ap]) = bridge a b := ey.symm.trans hy
    rw [hd] at hresult
    simpa [paddedWindow,l,r,List.append_assoc] using hresult
  rcases bridge_result j c d a b q hq hresult' with h | ⟨hj,h⟩
  · left; simpa [h,hframe] using hout
  · right; exact ⟨hj,by simpa [h] using hout⟩
end PhaseCases

end

/- ================= BRIDGE SEMANTICS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol FiniteCases LocalSyntax
namespace PhaseCases

def junctionBody (lead : Word) (alpha beta : List Letter) (j : Option Phase) (tail : Word) : Word :=
  lead ++ h alpha ++ junctionLeft j ++ punctuation j ++ [flat] ++ junctionRight j ++ hr beta ++ tail
private theorem last_split {w : List Letter} (hw : w ≠ []) : ∃ a c, w = a ++ [c] := by
  have hn : w.getLast? ≠ none := by simpa using hw
  cases he : w.getLast? with
  | none => exact (hn he).elim
  | some c => obtain ⟨a,ha⟩ := List.getLast?_eq_some_iff.mp he; exact ⟨a,c,ha⟩
private theorem left_padding (lead : Word) (a : List Letter)
    (hl : lead.getLast? = some dollar) :
    ∃ pre q, q ∈ [C,dollar] ∧ lead ++ h a = pre ++ [q] := by
  by_cases ha : a = []
  · subst a
    obtain ⟨pre,he⟩ := List.getLast?_eq_some_iff.mp hl
    exact ⟨pre,dollar,by simp,by simpa [h] using he⟩
  · obtain ⟨aa,c,rfl⟩ := last_split ha
    exact ⟨lead ++ h aa ++ [A,B c],C,by simp,by simp [h,List.append_assoc]⟩

/-- The dollar bridge changes punctuation and preserves the complete rows,
the right word, and the single common witness. -/
theorem bridge_preserves {x y : Word} (hx : Closure seeds x)
    (lead tail : Word) (alpha beta : List Letter) (j : Option Phase) (a b : Letter)
    (ha : alpha ≠ []) (hb : beta ≠ []) (hlast : lead.getLast? = some dollar)
    (hl : flat ∉ lead) (ht : flat ∉ tail)
    (hf : x = junctionBody lead alpha beta j tail) (hy : y = bridge a b)
    (rows blocks : List (List Letter))
    (hg : Soundness.Good (rows ++ [alpha]) beta blocks)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    ∃ j', pre ++ u ++ z ++ v ++ post = junctionBody lead alpha beta j' tail ∧
      Soundness.Good (rows ++ [alpha]) beta blocks := by
  obtain ⟨aa,c,rfl⟩ := last_split ha
  obtain ⟨bb,d,rfl⟩ := last_split hb
  obtain ⟨front,q,hq,hpad⟩ := left_padding lead aa hlast
  have hw : x = front ++ paddedWindow q j c d ++ (hr bb ++ tail) := by
    rw [hf]
    simp only [junctionBody,h,List.flatMap_append,hr,List.reverse_append]
    simpa [paddedWindow,h,hr,List.append_assoc] using
      congrArg (fun w => w ++ h [c] ++ junctionLeft j ++ punctuation j ++ [flat] ++
        junctionRight j ++ hr [d] ++ hr bb ++ tail) hpad
  have hfront : flat ∉ front := by
    have hn : flat ∉ lead ++ h aa := by simp [hl,h]
    rw [hpad] at hn
    exact fun hm => hn (List.mem_append_left _ hm)
  have htail : flat ∉ hr bb ++ tail := by simp [hr,ht]
  rcases bridge_insert hx j c d a b q hq front (hr bb ++ tail) hw hfront htail hy
      pre u v post z hu hv ex ey with he | ⟨_,he⟩
  · exact ⟨j,he.trans hf,hg⟩
  · refine ⟨none,?_,hg⟩
    rw [he]
    simpa [junctionBody,paddedWindow,h,hr,List.reverse_append,List.flatMap_append,
      List.append_assoc] using
      congrArg (fun w => w ++ h [c] ++ [sharp,dollar,flat] ++ hr [d] ++ hr bb ++ tail) hpad.symm
end PhaseCases

end

/- ================= LEFT CONTEXT ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace RowState
def lead (outer : Bool) (prior : List (List Letter)) : Word :=
  (if outer then [heart] else []) ++ [dollar] ++
    prior.flatMap (fun a => h a ++ [sharp,dollar])
theorem lead_flat_free (outer : Bool) (prior : List (List Letter)) : flat ∉ lead outer prior := by
  cases outer <;> simp [lead,h]

theorem lead_last (outer : Bool) (prior : List (List Letter)) :
    (lead outer prior).getLast? = some dollar := by
  have aux (ps : List (List Letter)) (front : Word) (hf : front.getLast? = some dollar) :
      (front ++ ps.flatMap (fun a => h a ++ [sharp,dollar])).getLast? = some dollar := by
    induction ps generalizing front with
    | nil => simpa using hf
    | cons a ps ih =>
      simpa only [List.flatMap_cons,List.append_assoc] using
        ih (front ++ (h a ++ [sharp,dollar])) (by simp [List.getLast?_append])
  exact aux prior ((if outer then [heart] else []) ++ [dollar])
    (by simp [List.getLast?_append])


end RowState

end

/- ================= RIGHT-TAIL TOKEN STREAMS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace TailTokens

/-- A general right tail is a stream of complete primed blocks and separator
symbols. This permits more separator arrangements than the paper needs. -/
inductive Token where
  | block (r : Word) | spade | club
  deriving DecidableEq

def start : Token → Symbol
  | .block _ => Cp | .spade => Symbol.spade | .club => Symbol.club
def interior : Token → Word
  | .block r => r ++ [Ap] | _ => []
def code (t : Token) : Word := start t :: interior t
def encode (ts : List Token) : Word := ts.flatMap code
@[simp] theorem encode_append (a b : List Token) : encode (a ++ b) = encode a ++ encode b := by
  simp [encode]

def Valid : Token → Prop
  | .block r => RightStructure.Raw r | _ => True
def AllValid (ts : List Token) : Prop := ∀ t ∈ ts, Valid t
def Initial (ts : List Token) : Prop := ∃ a rest, ts = Token.block [Bp a] :: rest

def boundary (a : Symbol) : Prop := a = Cp ∨ a = Symbol.spade ∨ a = Symbol.club

private theorem interior_free {t : Token} (ht : Valid t) {a : Symbol} (ha : boundary a) :
    a ∉ interior t := by
  cases t with
  | spade => simp [interior]
  | club => simp [interior]
  | block r =>
    have hn : a ∉ r := by
      intro hm
      have hr := ht.1 a hm
      rcases ha with rfl | rfl | rfl <;> simp [RightStructure.rawSymbol] at hr
    rcases ha with rfl | rfl | rfl <;> simp_all [interior]

/-- A marker-free segment can be skipped before a delimiter occurrence. -/
theorem after_free (a : Symbol) (front rest pre tail : Word)
    (hn : a ∉ front) (he : front ++ rest = pre ++ a :: tail) :
    ∃ q, pre = front ++ q ∧ rest = q ++ a :: tail := by
  induction front generalizing pre with
  | nil => exact ⟨pre,by simp,by simpa using he⟩
  | cons b front ih =>
    cases pre with
    | nil =>
      have hb : b = a := (List.cons.inj he).1
      subst b
      simp at hn
    | cons c pre =>
      have hb : b = c := (List.cons.inj he).1
      subst c
      obtain ⟨q,hq,hr⟩ := ih pre (fun hm => hn (by simp [hm])) (List.cons.inj he).2
      exact ⟨q,by simp [hq],hr⟩

/-- Every delimiter occurs at the start of exactly one token. -/
theorem prefix_cut (ts : List Token) (hv : AllValid ts) (a : Symbol) (ha : boundary a)
    (pre rest : Word) (he : encode ts = pre ++ a :: rest) :
    ∃ left t right, ts = left ++ t :: right ∧ pre = encode left ∧
      start t = a ∧ rest = interior t ++ encode right := by
  induction ts generalizing pre with
  | nil =>
    have hl := congrArg List.length he
    simp [encode] at hl
    omega
  | cons t ts ih =>
    have ht := hv t (by simp)
    have hvs : AllValid ts := fun q hq => hv q (by simp [hq])
    cases pre with
    | nil =>
      have hh : start t = a := (List.cons.inj he).1
      have hr : interior t ++ encode ts = rest := (List.cons.inj he).2
      exact ⟨[],t,ts,rfl,rfl,hh,hr.symm⟩
    | cons b pre =>
      have hb : start t = b := (List.cons.inj he).1
      have hr : interior t ++ encode ts = pre ++ a :: rest := (List.cons.inj he).2
      obtain ⟨q,hq,hrest⟩ := after_free a (interior t) (encode ts) pre rest
        (interior_free ht ha) hr
      obtain ⟨left,u,right,hts,hpre,hu,hright⟩ := ih hvs q hrest
      refine ⟨t :: left,u,right,by simp [hts],?_,hu,hright⟩
      simp [encode,code,hq,hpre,hb]

/-- A trailing context without the start marker does not affect parsing. -/
theorem prefix_cut_trailer (ts : List Token) (hv : AllValid ts) (a : Symbol) (ha : boundary a)
    (trail pre rest : Word) (ht : a ∉ trail) (he : encode ts ++ trail = pre ++ a :: rest) :
    ∃ left t right, ts = left ++ t :: right ∧ pre = encode left ∧
      start t = a ∧ rest = interior t ++ encode right ++ trail := by
  induction ts generalizing pre with
  | nil =>
    have he' : trail = pre ++ a :: rest := by simpa [encode] using he
    exact (ht (by rw [he']; simp)).elim
  | cons t ts ih =>
    have ht' := hv t (by simp)
    have hvs : AllValid ts := fun q hq => hv q (by simp [hq])
    cases pre with
    | nil =>
      have hh : start t = a := (List.cons.inj he).1
      have hr : interior t ++ encode ts ++ trail = rest := by
        simpa [encode,code,List.append_assoc] using (List.cons.inj he).2
      exact ⟨[],t,ts,rfl,rfl,hh,hr.symm⟩
    | cons b pre =>
      have hb : start t = b := (List.cons.inj he).1
      have hr : interior t ++ (encode ts ++ trail) = pre ++ a :: rest := by
        simpa [encode,code,List.append_assoc] using (List.cons.inj he).2
      obtain ⟨q,hq,hrest⟩ := after_free a (interior t) (encode ts ++ trail) pre rest
        (interior_free ht' ha) hr
      obtain ⟨left,u,right,hts,hpre,hu,hright⟩ := ih hvs q hrest
      refine ⟨t :: left,u,right,by simp [hts],?_,hu,hright⟩
      simp [encode,code,hq,hpre,hb]

theorem marker_interior {t : Token} {a : Symbol} (ha : a = Symbol.club ∨ a = Symbol.spade)
    (ht : start t = a) : interior t = [] := by
  rcases ha with rfl | rfl <;> cases t <;> simp_all [start,interior]

/-- A cut after a one-symbol separator is also a token boundary. -/
theorem suffix_cut (ts : List Token) (hv : AllValid ts) (a : Symbol)
    (ha : a = Symbol.club ∨ a = Symbol.spade)
    (pre post : Word) (he : encode ts = pre ++ a :: post) :
    ∃ left t right, ts = left ++ t :: right ∧ pre = encode left ∧ post = encode right := by
  have hb : boundary a := by rcases ha with rfl | rfl <;> simp [boundary]
  obtain ⟨left,t,right,hdec,hpre,ht,hpost⟩ := prefix_cut ts hv a hb pre post he
  exact ⟨left,t,right,hdec,hpre,by simpa [marker_interior ha ht] using hpost⟩

end TailTokens

end

/- ================= TERMINAL REPLACEMENT ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace TailTokens

private theorem valid_parts {ts left rest front right donor : List Token}
    (hv : AllValid ts) (hl : ts = left ++ rest) (hr : ts = front ++ right)
    (hd : AllValid donor) : AllValid (left ++ donor ++ right) := by
  intro t hm
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact hv t (by rw [hl]; exact List.mem_append_left _ hm)
  · exact hd t hm
  · exact hv t (by rw [hr]; exact List.mem_append_right _ hm)

private theorem initial_parts {ts left rest donor right : List Token}
    (hi : Initial ts) (hl : ts = left ++ rest) (hd : left ≠ [] ∨ Initial donor) :
    Initial (left ++ donor ++ right) := by
  cases left with
  | nil =>
    obtain ⟨a,tail,he⟩ := hd.resolve_left (by simp)
    exact ⟨a,tail ++ right,by simp [he]⟩
  | cons t left =>
    obtain ⟨a,tail,he⟩ := hi
    have ht : t = Token.block [Bp a] := (List.cons.inj (he.symm.trans hl)).1.symm
    subst t
    exact ⟨a,left ++ donor ++ right,by simp [List.append_assoc]⟩

theorem encode_no_diamond {ts : List Token} (hv : AllValid ts) : diamond ∉ encode ts := by
  intro hm
  obtain ⟨t,ht,hmt⟩ := List.mem_flatMap.mp hm
  have hv' := hv t ht
  cases t with
  | spade => simp [code,start,interior] at hmt
  | club => simp [code,start,interior] at hmt
  | block r =>
    have hmr : diamond ∈ r := by simpa [code,start,interior] using hmt
    have hn := hv'.1 diamond hmr
    simp [RightStructure.rawSymbol] at hn

/-- A donor ending at the unique outer diamond replaces a token suffix. -/
theorem replace_terminal {ts donor : List Token}
    (hv : AllValid ts) (hi : Initial ts) (hd : AllValid donor) (hdinit : Initial donor)
    (pre middle post : Word)
    (he : encode ts ++ [natural,diamond] = pre ++ Cp :: middle ++ diamond :: post) :
    ∃ result, AllValid result ∧ Initial result ∧
      pre ++ encode donor ++ [natural,diamond] ++ post = encode result ++ [natural,diamond] := by
  have hp : post = [] := BlockBoundaries.terminal_marker diamond (encode ts ++ [natural])
    (pre ++ Cp :: middle) post (by simp [encode_no_diamond hv])
    (by simpa [List.append_assoc] using he)
  obtain ⟨left,t,right,hleft,hpre,_,_⟩ := prefix_cut_trailer ts hv Cp (by simp [boundary])
    [natural,diamond] pre (middle ++ diamond :: post) (by simp)
    (by simpa [List.append_assoc] using he)
  refine ⟨left ++ donor,?_,?_,?_⟩
  · simpa using valid_parts hv hleft (show ts = ts ++ [] by simp) hd
  · simpa using initial_parts (right := []) hi hleft (Or.inr hdinit)
  · simp [hpre,hp,encode,List.flatMap_append,List.append_assoc]

end TailTokens

end

/- ================= TOKEN DECODING ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol Soundness
namespace TailTokens

def choices : Token → List (List Letter)
  | .block r => [RightStructure.payloadLetters r] | _ => []
def blockLists (ts : List Token) : List (List Letter) := ts.flatMap choices

theorem projection {ts : List Token} (hv : AllValid ts) :
    (encode ts).filterMap rightProjection = packed (blockLists ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have ht := hv t (by simp)
    have hi := ih (fun t hm => hv t (by simp [hm]))
    cases t with
    | club => simpa [encode,code,start,interior,blockLists,choices,rightProjection] using hi
    | spade => simpa [encode,code,start,interior,blockLists,choices,rightProjection] using hi
    | block r =>
      have hp := RightStructure.payload_projection (p := r ++ [Ap,Symbol.spade]) ⟨r,ht,rfl⟩
      have hc : (code (Token.block r)).filterMap rightProjection =
          (RightStructure.payloadLetters r).map some ++ [none] := by
        simpa [code,start,interior,rightProjection,RightStructure.payloadLetters,List.filterMap_append] using hp
      change (code (Token.block r) ++ encode ts).filterMap rightProjection =
        packed (RightStructure.payloadLetters r :: blockLists ts)
      rw [List.filterMap_append,hc,hi]
      simp [packed,List.append_assoc]

theorem blocks_nonempty {ts : List Token} (hv : AllValid ts) :
    ∀ b ∈ blockLists ts, b ≠ [] := by
  intro b hb
  obtain ⟨t,ht,hbt⟩ := List.mem_flatMap.mp hb
  have hv' := hv t ht
  cases t with
  | club => simp [choices] at hbt
  | spade => simp [choices] at hbt
  | block r =>
    have he : b = RightStructure.payloadLetters r := by simpa [choices] using hbt
    subst b
    obtain ⟨a,ha⟩ := hv'.2
    have hm : a ∈ RightStructure.payloadLetters r := List.mem_filterMap.mpr ⟨Bp a,ha,rfl⟩
    intro he
    simpa [he] using hm

def Good (rows : List (List Letter)) (ts : List Token) : Prop :=
  Soundness.Good rows [] (blockLists ts).reverse

/-- A single common witness is extended along an embedding of complete tails. -/
theorem good_monotone {old ts : List Token} {rows : List (List Letter)}
    (ho : AllValid old) (hn : AllValid ts) (hs : (encode old).Sublist (encode ts))
    (hg : Good rows old) : Good rows ts := by
  obtain ⟨w,hw,hr⟩ := hg
  obtain ⟨v,hv,hsub⟩ := raw_tail_monotone (oldBeta := []) (beta := [])
    (oldBlocks := (blockLists old).reverse) (blocks := (blockLists ts).reverse)
    (by simpa using projection ho) (by simpa using projection hn)
    (fun b hb => blocks_nonempty hn b (List.mem_reverse.mp hb)) hs hw
  refine ⟨v,hv,?_⟩
  intro r hm
  exact (hr r hm).trans (by simpa using hsub)

def singletonTokens (beta : List Letter) : List Token :=
  beta.reverse.map (fun a => Token.block [Bp a])

theorem encode_singletons (beta : List Letter) : encode (singletonTokens beta) = hr beta := by
  unfold encode singletonTokens hr
  rw [List.flatMap_map]
  rfl
theorem singletons_valid (beta : List Letter) : AllValid (singletonTokens beta) := by
  intro t ht
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp ht
  exact ⟨by simp [RightStructure.rawSymbol],⟨a,by simp⟩⟩
theorem singletons_initial {beta : List Letter} (hb : beta ≠ []) : Initial (singletonTokens beta) := by
  cases he : beta.reverse with
  | nil => exact (hb (by simpa using congrArg List.reverse he)).elim
  | cons a tail => exact ⟨a,tail.map (fun b => Token.block [Bp b]),by simp [singletonTokens,he]⟩

theorem singleton_blocks (beta : List Letter) :
    blockLists (singletonTokens beta) = beta.reverse.map (fun a => [a]) := by
  unfold blockLists singletonTokens
  rw [List.flatMap_map]
  change beta.reverse.flatMap (fun a => [[a]]) = beta.reverse.map (fun a => [a])
  rw [← List.map_eq_flatMap]

@[simp] theorem blockLists_append (a b : List Token) :
    blockLists (a ++ b) = blockLists a ++ blockLists b := by simp [blockLists]

private theorem chooses_append {α : Type} {bs cs : List (List α)} {w v : List α}
    (hw : Chooses bs w) (hv : Chooses cs v) : Chooses (bs ++ cs) (w ++ v) := by
  induction hw with
  | nil => exact hv
  | cons h _ ih => exact .cons h ih
private theorem chooses_singletons (beta : List Letter) : Chooses (beta.map (fun a => [a])) beta := by
  induction beta with
  | nil => exact .nil
  | cons a beta ih => exact .cons (by simp) ih
theorem chooses_last {bs : List (List Letter)} {a : Letter} {w : List Letter}
    (hw : Chooses (bs ++ [[a]]) w) : ∃ v, Chooses bs v ∧ w = v ++ [a] := by
  induction bs generalizing w with
  | nil =>
    cases hw with
    | cons ha h => cases h; exact ⟨[],.nil,by simpa using ha⟩
  | cons b bs ih =>
    cases hw with
    | cons ha h =>
      obtain ⟨v,hv,he⟩ := ih h
      exact ⟨_ :: v,.cons ha hv,by simp [he]⟩

/-- Move a concrete unmarked suffix into singleton choice blocks. -/
theorem good_concrete {rows : List (List Letter)} {beta : List Letter} {ts : List Token}
    (hg : Soundness.Good rows beta (blockLists ts).reverse) :
    Good rows (singletonTokens beta ++ ts) := by
  obtain ⟨w,hw,hr⟩ := hg
  refine ⟨w ++ beta,?_,?_⟩
  · simpa only [blockLists_append,singleton_blocks,List.reverse_append,
      ← List.map_reverse,List.reverse_reverse] using chooses_append hw (chooses_singletons beta)
  · simpa using hr

/-- The first physical singleton is the concrete suffix of the decoded word. -/
theorem good_initial {rows : List (List Letter)} {a : Letter} {ts : List Token}
    (hg : Good rows (Token.block [Bp a] :: ts)) :
    Soundness.Good rows [a] (blockLists ts).reverse := by
  obtain ⟨w,hw,hr⟩ := hg
  have hw' : Chooses ((blockLists ts).reverse ++ [[a]]) w := by
    simpa [blockLists,choices,RightStructure.payloadLetters] using hw
  obtain ⟨v,hv,rfl⟩ := chooses_last hw'
  exact ⟨v,hv,by simpa using hr⟩

end TailTokens

end

/- ================= REPLACEMENT IN CONTEXT ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace TailTokens

/-- The new stream retains a prefix and a suffix of the host stream. -/
def Splice (old donor result : List Token) : Prop :=
  ∃ left right, result = left ++ donor ++ right ∧
    (∃ rest, old = left ++ rest) ∧ (∃ front, old = front ++ right)

theorem splice_inherits {old donor result : List Token} (hs : Splice old donor result)
    (P : Token → Prop) (ho : ∀ t ∈ old, P t) (hd : ∀ t ∈ donor, P t) : ∀ t ∈ result, P t := by
  obtain ⟨left,right,rfl,⟨rest,hl⟩,⟨front,hr⟩⟩ := hs
  intro t hm
  simp only [List.mem_append] at hm
  rcases hm with (hm | hm) | hm
  · exact ho t (by rw [hl]; exact List.mem_append_left _ hm)
  · exact hd t hm
  · exact ho t (by rw [hr]; exact List.mem_append_right _ hm)

private theorem initial_splice {old left rest donor right : List Token}
    (hi : Initial old) (hl : old = left ++ rest) (hd : left ≠ [] ∨ Initial donor) :
    Initial (left ++ donor ++ right) := by
  cases left with
  | nil =>
    obtain ⟨a,tail,he⟩ := hd.resolve_left (by simp)
    exact ⟨a,tail ++ right,by simp [he]⟩
  | cons t left =>
    obtain ⟨a,tail,he⟩ := hi
    have ht : t = Token.block [Bp a] := (List.cons.inj (he.symm.trans hl)).1.symm
    subst t
    exact ⟨a,left ++ donor ++ right,by simp [List.append_assoc]⟩

/-- Separator replacement inside a tail with arbitrary marker-free trailer. -/
theorem separator_context {ts donor : List Token}
    (hv : AllValid ts) (hi : Initial ts) (hd : AllValid donor)
    (a b : Symbol) (ha : boundary a) (hb : b = Symbol.club ∨ b = Symbol.spade)
    (hdinit : Initial donor ∨ a ≠ Cp)
    (trail pre middle post : Word) (hta : a ∉ trail) (htb : b ∉ trail)
    (he : encode ts ++ trail = pre ++ a :: middle ++ b :: post) :
    ∃ result, AllValid result ∧ Initial result ∧ Splice ts donor result ∧
      pre ++ encode donor ++ post = encode result ++ trail := by
  obtain ⟨left,t,rest,hleft,hpre,ht,_⟩ := prefix_cut_trailer ts hv a ha trail
    pre (middle ++ b :: post) hta (by simpa [List.append_assoc] using he)
  have hbb : boundary b := by rcases hb with rfl | rfl <;> simp [boundary]
  obtain ⟨front,u,right,hright,_,hu,hpost⟩ := prefix_cut_trailer ts hv b hbb trail
    (pre ++ a :: middle) post htb he
  have hpost' : post = encode right ++ trail := by simpa [marker_interior hb hu] using hpost
  have hinit : left ≠ [] ∨ Initial donor := by
    rcases hdinit with hdinit | hne
    · exact Or.inr hdinit
    · left
      intro hl
      obtain ⟨c,tail,hc⟩ := hi
      have he' : ts = t :: rest := by simpa [hl] using hleft
      have ht' : t = Token.block [Bp c] := (List.cons.inj (hc.symm.trans he')).1.symm
      exact hne (by simpa [ht',start] using ht.symm)
  have hs : Splice ts donor (left ++ donor ++ right) :=
    ⟨left,right,rfl,⟨_,hleft⟩,⟨front ++ [u],by simpa [List.append_assoc] using hright⟩⟩
  refine ⟨left ++ donor ++ right,splice_inherits hs Valid hv hd,initial_splice hi hleft hinit,hs,?_⟩
  simp [hpre,hpost',encode,List.flatMap_append,List.append_assoc]

/-- Cp-to-Cp replacement retains the next token and the external trailer. -/
theorem start_context {ts donor : List Token}
    (hv : AllValid ts) (hi : Initial ts) (hd : AllValid donor) (hdinit : Initial donor)
    (trail pre middle post : Word) (ht : Cp ∉ trail)
    (he : encode ts ++ trail = pre ++ Cp :: middle ++ Cp :: post) :
    ∃ result, AllValid result ∧ Initial result ∧ Splice ts donor result ∧
      pre ++ encode donor ++ Cp :: post = encode result ++ trail := by
  obtain ⟨left,t,rest,hleft,hpre,_,_⟩ := prefix_cut_trailer ts hv Cp (by simp [boundary])
    trail pre (middle ++ Cp :: post) ht (by simpa [List.append_assoc] using he)
  obtain ⟨front,u,right,hright,_,hu,hpost⟩ := prefix_cut_trailer ts hv Cp (by simp [boundary])
    trail (pre ++ Cp :: middle) post ht he
  have hs : Splice ts donor (left ++ donor ++ u :: right) :=
    ⟨left,u :: right,rfl,⟨_,hleft⟩,⟨_,hright⟩⟩
  refine ⟨left ++ donor ++ u :: right,splice_inherits hs Valid hv hd,
    initial_splice hi hleft (Or.inr hdinit),hs,?_⟩
  simp [hpre,hpost,encode,code,hu,List.flatMap_append,List.append_assoc]

end TailTokens

end

/- ================= TOKENIZING GENERATED DONORS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol
namespace TailTokens

private theorem payload_tokens (ps : List Word)
    (hp : ∀ p ∈ ps, RightStructure.Payload p) :
    ∃ ts, AllValid ts ∧ BlockBoundaries.encode Cp Symbol.club ps = encode ts := by
  induction ps with
  | nil => exact ⟨[],by simp [AllValid],rfl⟩
  | cons p ps ih =>
    obtain ⟨r,hr,rfl⟩ := hp p (by simp)
    obtain ⟨ts,hv,he⟩ := ih (fun p hm => hp p (by simp [hm]))
    refine ⟨Token.block r :: Token.spade :: Token.club :: ts,?_,?_⟩
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | rfl | rfl | ht
      · exact hr
      · trivial
      · trivial
      · exact hv t ht
    · simp [BlockBoundaries.encode,encode,code,start,interior,List.append_assoc] at he ⊢
      exact he

/-- The independently proved marked-donor classification supplies a valid
stream beginning with a concrete singleton block. -/
theorem right_tokens {w : Word} {flag : Bool} (hw : RightStructure.Inv w flag) :
    ∃ ts, AllValid ts ∧ Initial ts ∧ w = encode ts ++ RightStructure.terminal flag := by
  obtain ⟨ps,⟨a,rest,rfl⟩,hp,rfl⟩ := hw
  obtain ⟨ts,hv,he⟩ := payload_tokens rest (fun p hm => hp p (by simp [hm]))
  refine ⟨Token.block [Bp a] :: Token.spade :: Token.club :: ts,?_,⟨a,_,rfl⟩,?_⟩
  · intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | rfl | ht
    · exact ⟨by simp [RightStructure.rawSymbol],⟨a,by simp⟩⟩
    · trivial
    · trivial
    · exact hv t ht
  · simp [BlockBoundaries.encode,RightStructure.initial,encode,code,start,interior,
      List.append_assoc] at he ⊢
    exact he

theorem type_one_tokens {w : Word} (hw : Closure seeds w)
    (he : FiniteCases.ends w = (some Cp,some Cp)) :
    ∃ ts, AllValid ts ∧ Initial ts ∧ w = encode ts ++ [Cp] := by
  obtain ⟨beta,hb,rfl⟩ := TypeOne.generated_one_shape hw he
  have hn : beta ≠ [] := by intro he; simp [he] at hb
  exact ⟨singletonTokens beta,singletons_valid beta,singletons_initial hn,
    by rw [encode_singletons]⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem mask_filter : ∀ w ∈ FiniteCases.small,
    FiniteCases.ends w = (some Symbol.club,some Symbol.spade) → w ∈ RightStructure.maskSeeds := by
  decide +kernel

theorem mask_tokens {w : Word} (hw : Closure seeds w)
    (he : FiniteCases.ends w = (some Symbol.club,some Symbol.spade)) :
    ∃ ts, AllValid ts ∧ w = encode ts := by
  have hs := FiniteCases.generated_small hw (by simp [he,FiniteCases.smallEnd])
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp (mask_filter w hs he)
  have heq : w = [Symbol.club,Cp] ++ theta (i.val+1) ++ [Ap,Symbol.spade] := hi.symm
  refine ⟨[Token.club,Token.block (theta (i.val+1)),Token.spade],?_,?_⟩
  · intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl
    · trivial
    · constructor
      · intro c hc
        simp only [theta,List.mem_cons,List.mem_map] at hc
        rcases hc with rfl | ⟨a,_,rfl⟩ <;> rfl
      · refine ⟨none,?_⟩
        change Bp none ∈ extraB :: Bp none :: _
        simp
    · trivial
  · simpa [encode,code,start,interior,List.append_assoc] using heq

end TailTokens

end

/- ================= THE COMMON-WITNESS INVARIANT ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens
namespace TokenState

def Simple (ts : List Token) : Prop := ∀ t ∈ ts, ∃ a, t = Token.block [Bp a]
structure State where
  outer : Bool
  prior : List (List Letter)
  last : List Letter
  j : Option Phase
  tokens : List Token

def ending (outer : Bool) : Word := [natural] ++ if outer then [diamond] else []
def word (s : State) : Word := junctionBody (RowState.lead s.outer s.prior)
  s.last [] s.j (encode s.tokens ++ ending s.outer)
structure Valid (s : State) : Prop where
  last_ne : s.last ≠ []
  prior_ne : ∀ a ∈ s.prior, a ≠ []
  tokens_valid : AllValid s.tokens
  initial : Initial s.tokens
  simple : s.outer = false → Simple s.tokens
  good : TailTokens.Good (s.prior ++ [s.last]) s.tokens

def Invariant (w : Word) : Prop := ∃ s, Valid s ∧ w = word s

theorem encode_flat_free {ts : List Token} (hv : AllValid ts) : flat ∉ encode ts := by
  intro hm
  obtain ⟨t,ht,hm⟩ := List.mem_flatMap.mp hm
  have hv' := hv t ht
  cases t with
  | spade => simp [code,start,interior] at hm
  | club => simp [code,start,interior] at hm
  | block r =>
    have hmr : flat ∈ r := by simpa [code,start,interior] using hm
    have hn := hv'.1 flat hmr
    simp [RightStructure.rawSymbol] at hn

theorem ending_flat_free (outer : Bool) : flat ∉ ending outer := by cases outer <;> decide
theorem singleton_simple (beta : List Letter) : Simple (singletonTokens beta) := by
  intro t ht
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp ht
  exact ⟨a,rfl⟩
private theorem valid_append {a b : List Token} (ha : AllValid a) (hb : AllValid b) : AllValid (a ++ b) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (ha t) (hb t)
private theorem simple_append {a b : List Token} (ha : Simple a) (hb : Simple b) : Simple (a ++ b) := by
  intro t ht
  exact (List.mem_append.mp ht).elim (ha t) (hb t)
private theorem split_last {w : List Letter} (hw : w ≠ []) : ∃ a c, w = a ++ [c] := by
  have hn : w.getLast? ≠ none := by simpa using hw
  cases he : w.getLast? with
  | none => exact (hn he).elim
  | some c => obtain ⟨a,ha⟩ := List.getLast?_eq_some_iff.mp he; exact ⟨a,c,ha⟩

/-- Phase preservation for the more general token-stream invariant. -/
theorem phase_closed {x y : Word} (hx : Closure seeds x) (hi : Invariant x)
    (e : Letter) (hy : y ∈ Completion.donors e)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨s,hs,hword⟩ := hi
  obtain ⟨d,rest,htokens⟩ := hs.initial
  have hrest : AllValid rest := fun t ht => hs.tokens_valid t (by rw [htokens]; simp [ht])
  have htail : flat ∉ encode rest ++ ending s.outer := by
    simp [encode_flat_free hrest,ending_flat_free]
  cases hj : s.j with
  | some p =>
    have hf : x = body (RowState.lead s.outer s.prior) s.last [d] p
        (encode rest ++ ending s.outer) := by
      simpa [word,junctionBody,body,hj,htokens,encode,code,start,interior,hr,
        junctionLeft,junctionRight,punctuation,List.append_assoc] using hword
    have hg := good_initial (by simpa [htokens] using hs.good)
    obtain ⟨p',alpha,beta,ha,hb,he,hg'⟩ := phase_preserves hx
      (RowState.lead s.outer s.prior) (encode rest ++ ending s.outer)
      s.last [d] p e s.prior (blockLists rest).reverse hs.last_ne (by simp)
      (RowState.lead_flat_free _ _) htail hf hg hy pre u v post z hu hv ex ey
    let s' : State := {s with last := alpha, j := some p', tokens := singletonTokens beta ++ rest}
    have hs' : Valid s' := by
      refine ⟨ha,hs.prior_ne,valid_append (singletons_valid beta) hrest,?_,?_,?_⟩
      · obtain ⟨a,ts,he⟩ := singletons_initial hb
        exact ⟨a,ts ++ rest,by simp [s',he,List.append_assoc]⟩
      · intro hout
        apply simple_append (singleton_simple beta)
        intro t ht
        exact hs.simple hout t (by rw [htokens]; simp [ht])
      · exact good_concrete hg'
    refine ⟨s',hs',?_⟩
    simpa [word,s',body,junctionBody,junctionLeft,junctionRight,punctuation,
      encode_append,encode_singletons,hr,List.append_assoc] using he
  | none =>
    obtain ⟨a,c,ha⟩ := split_last hs.last_ne
    have hf : x = (RowState.lead s.outer s.prior ++ h a) ++ finishedWindow c d ++
        (encode rest ++ ending s.outer) := by
      simpa [word,junctionBody,hj,htokens,ha,finishedWindow,encode,code,start,interior,
        junctionLeft,junctionRight,punctuation,h,hr,List.flatMap_append,List.append_assoc] using hword
    exact (finished_no_phase hx c d e hy _ _ hf
      (by simp [RowState.lead_flat_free,h]) htail pre u v post z hu hv ex ey).elim

/-- Bridge preservation uses the same rows and the same token choices. -/
theorem bridge_closed {x y : Word} (hx : Closure seeds x) (hi : Invariant x)
    (a b : Letter) (hy : y = bridge a b)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨s,hs,hword⟩ := hi
  obtain ⟨d,rest,htokens⟩ := hs.initial
  have hrest : AllValid rest := fun t ht => hs.tokens_valid t (by rw [htokens]; simp [ht])
  have hf : x = junctionBody (RowState.lead s.outer s.prior) s.last [d] s.j
      (encode rest ++ ending s.outer) := by
    simpa [word,junctionBody,htokens,encode,code,start,interior,hr,List.append_assoc] using hword
  have hg := good_initial (by simpa [htokens] using hs.good)
  obtain ⟨j',he,_⟩ := bridge_preserves hx (RowState.lead s.outer s.prior)
    (encode rest ++ ending s.outer) s.last [d] s.j a b hs.last_ne (by simp)
    (RowState.lead_last _ _) (RowState.lead_flat_free _ _)
    (by simp [encode_flat_free hrest,ending_flat_free]) hf hy s.prior (blockLists rest).reverse hg
    pre u v post z hu hv ex ey
  let s' : State := {s with j := j'}
  refine ⟨s',⟨hs.last_ne,hs.prior_ne,hs.tokens_valid,hs.initial,hs.simple,hs.good⟩,?_⟩
  simpa [word,s',junctionBody,htokens,encode,code,start,interior,hr,List.append_assoc] using he

end TokenState

end

/- ================= TYPE-1 PRESERVATION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens
namespace TokenState

def left (s : State) : Word := RowState.lead s.outer s.prior ++ h s.last ++ junctionLeft s.j ++
  punctuation s.j ++ [flat] ++ junctionRight s.j

theorem word_eq (s : State) : word s = left s ++ encode s.tokens ++ ending s.outer := by
  simp [word,left,junctionBody,hr,List.append_assoc]

theorem left_free (s : State) (a : Symbol) (ha : boundary a) : a ∉ left s := by
  rcases ha with rfl | rfl | rfl <;>
    cases hj : s.j with
    | none => cases s.outer <;> simp [left,RowState.lead,hj,junctionLeft,junctionRight,punctuation,h]
    | some p => cases p <;> cases s.outer <;>
        simp [left,RowState.lead,hj,junctionLeft,junctionRight,punctuation,phaseLeft,phaseRight,h]

theorem ending_boundary_free (outer : Bool) (a : Symbol) (ha : boundary a) : a ∉ ending outer := by
  rcases ha with rfl | rfl | rfl <;> cases outer <;> decide

private theorem insertion_sublist (pre u v post z : Word) :
    (pre ++ u ++ v ++ post).Sublist (pre ++ u ++ z ++ v ++ post) := by
  simpa [List.append_assoc] using
    (((List.sublist_append_right z v).append_left u).append_left pre).append_right post

/-- Once a right-donor case supplies the new token stream, syntax and the
single shared semantic witness are both preserved. -/
theorem finish_right {x : Word} (s : State) (hs : Valid s) (hword : x = word s)
    (pre u v post z : Word) (ex : x = pre ++ u ++ v ++ post)
    (result : List Token) (hv : AllValid result) (hi : Initial result)
    (hc : s.outer = false → Simple result)
    (hout : pre ++ u ++ z ++ v ++ post = left s ++ encode result ++ ending s.outer) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  have hfull := insertion_sublist pre u v post z
  have hold : pre ++ u ++ v ++ post = left s ++ encode s.tokens ++ ending s.outer :=
    ex.symm.trans (hword.trans (word_eq s))
  rw [hold,hout] at hfull
  have hfull' : (left s ++ (encode s.tokens ++ ending s.outer)).Sublist
      (left s ++ (encode result ++ ending s.outer)) := by
    simpa only [List.append_assoc] using hfull
  have htail := (List.append_sublist_append_right (ending s.outer)).mp
    ((List.append_sublist_append_left (left s)).mp hfull')
  let s' : State := {s with tokens := result}
  refine ⟨s',⟨hs.last_ne,hs.prior_ne,hv,hi,hc,good_monotone hs.tokens_valid hv htail hs.good⟩,?_⟩
  simpa [word_eq,left,s'] using hout

/-- Every generated Cp-to-Cp donor preserves the row invariant. -/
theorem type_one_closed {x y : Word} (hi : Invariant x) (hy : Closure seeds y)
    (hyend : FiniteCases.ends y = (some Cp,some Cp))
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨s,hs,hword⟩ := hi
  obtain ⟨beta,hbeta,hyshape⟩ := TypeOne.generated_one_shape hy hyend
  have hb : beta ≠ [] := by intro he; simp [he] at hbeta
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends Cp Cp y u z v hu hv ey hyend
  have hfactor : left s ++ (encode s.tokens ++ ending s.outer) =
      pre ++ Cp :: (us ++ vs ++ Cp :: post) := by
    simpa [word_eq,List.append_assoc] using hword.symm.trans ex
  obtain ⟨pre',hpre,hrest⟩ := after_free Cp (left s) (encode s.tokens ++ ending s.outer)
    pre _ (left_free s Cp (by simp [boundary])) hfactor
  obtain ⟨result,hvalid,hinit,hsplice,hresult⟩ := start_context hs.tokens_valid hs.initial
    (singletons_valid beta) (singletons_initial hb) (ending s.outer) pre' (us ++ vs) post
    (ending_boundary_free _ Cp (by simp [boundary]))
    (by simpa [List.append_assoc] using hrest)
  have hout : pre ++ (Cp :: us) ++ z ++ (vs ++ [Cp]) ++ post =
      left s ++ encode result ++ ending s.outer := by
    calc
      _ = pre ++ y ++ post := by simp [ey,List.append_assoc]
      _ = left s ++ (pre' ++ encode (singletonTokens beta) ++ Cp :: post) := by
        simp [hpre,hyshape,encode_singletons,List.append_assoc]
      _ = _ := by rw [hresult]; simp [List.append_assoc]
  exact finish_right s hs hword pre (Cp :: us) (vs ++ [Cp]) post z ex result hvalid hinit
    (fun hout => splice_inherits hsplice (fun t => ∃ a, t = Token.block [Bp a])
      (hs.simple hout) (singleton_simple beta)) hout

end TokenState

end

/- ================= MARKED RIGHT AND MASK PRESERVATION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens
namespace TokenState

theorem simple_no_club {ts : List Token} (hs : Simple ts) : Symbol.club ∉ encode ts := by
  intro hm
  obtain ⟨t,ht,hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨a,rfl⟩ := hs t ht
  simp [code,start,interior] at hm

private theorem unframed_no_club {s : State} (hs : Valid s) (hf : s.outer = false) :
    Symbol.club ∉ word s := by
  rw [word_eq]
  simp [left_free s Symbol.club (by simp [boundary]),simple_no_club (hs.simple hf),ending,hf]

private theorem club_tokens {y : Word} (hy : Closure seeds y)
    (he : FiniteCases.ends y = (some Cp,some Symbol.club)) :
    ∃ donor, AllValid donor ∧ Initial donor ∧ y = encode donor := by
  obtain ⟨flag,hflag⟩ := RightStructure.generated_right hy (by simp [RightStructure.rightEnd,he])
  have heq := RightStructure.inv_ends hflag
  cases flag with
  | true => simp [he] at heq
  | false =>
    obtain ⟨ts,hv,hi,ht⟩ := right_tokens hflag
    exact ⟨ts,hv,hi,by simpa [RightStructure.terminal] using ht⟩

private theorem diamond_tokens {y : Word} (hy : Closure seeds y)
    (he : FiniteCases.ends y = (some Cp,some diamond)) :
    ∃ donor, AllValid donor ∧ Initial donor ∧ y = encode donor ++ [natural,diamond] := by
  obtain ⟨flag,hflag⟩ := RightStructure.generated_right hy (by simp [RightStructure.rightEnd,he])
  have heq := RightStructure.inv_ends hflag
  cases flag with
  | false => simp [he] at heq
  | true =>
    obtain ⟨ts,hv,hi,ht⟩ := right_tokens hflag
    exact ⟨ts,hv,hi,by simpa [RightStructure.terminal] using ht⟩

/-- Marked Cp-to-club donors replace complete tokens. -/
theorem club_closed {x y : Word} (hi : Invariant x) (hy : Closure seeds y)
    (hyend : FiniteCases.ends y = (some Cp,some Symbol.club))
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨s,hs,hword⟩ := hi
  obtain ⟨donor,hd,hdi,hyshape⟩ := club_tokens hy hyend
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends Cp Symbol.club y u z v hu hv ey hyend
  have hfactor : left s ++ (encode s.tokens ++ ending s.outer) =
      pre ++ Cp :: (us ++ vs ++ Symbol.club :: post) := by
    simpa [word_eq,List.append_assoc] using hword.symm.trans ex
  obtain ⟨pre',hpre,hrest⟩ := after_free Cp (left s) (encode s.tokens ++ ending s.outer)
    pre _ (left_free s Cp (by simp [boundary])) hfactor
  obtain ⟨result,hvalid,hinit,_,hresult⟩ := separator_context hs.tokens_valid hs.initial hd
    Cp Symbol.club (by simp [boundary]) (Or.inl rfl) (Or.inl hdi)
    (ending s.outer) pre' (us ++ vs) post
    (ending_boundary_free _ Cp (by simp [boundary]))
    (ending_boundary_free _ Symbol.club (by simp [boundary]))
    (by simpa [List.append_assoc] using hrest)
  have hout : pre ++ (Cp :: us) ++ z ++ (vs ++ [Symbol.club]) ++ post =
      left s ++ encode result ++ ending s.outer := by
    calc
      _ = pre ++ y ++ post := by simp [ey,List.append_assoc]
      _ = left s ++ (pre' ++ encode donor ++ post) := by simp [hpre,hyshape,List.append_assoc]
      _ = _ := by rw [hresult]; simp [List.append_assoc]
  apply finish_right s hs hword pre (Cp :: us) (vs ++ [Symbol.club]) post z ex result hvalid hinit _ hout
  intro hf
  have hm : Symbol.club ∈ x := by rw [ex]; simp
  exact (unframed_no_club hs hf (hword ▸ hm)).elim

/-- A generated mask can only replace complete tokens between separators. -/
theorem mask_closed {x y : Word} (hi : Invariant x) (hy : Closure seeds y)
    (hyend : FiniteCases.ends y = (some Symbol.club,some Symbol.spade))
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨s,hs,hword⟩ := hi
  obtain ⟨donor,hd,hyshape⟩ := mask_tokens hy hyend
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends Symbol.club Symbol.spade y u z v hu hv ey hyend
  have hfactor : left s ++ (encode s.tokens ++ ending s.outer) =
      pre ++ Symbol.club :: (us ++ vs ++ Symbol.spade :: post) := by
    simpa [word_eq,List.append_assoc] using hword.symm.trans ex
  obtain ⟨pre',hpre,hrest⟩ := after_free Symbol.club (left s) (encode s.tokens ++ ending s.outer)
    pre _ (left_free s Symbol.club (by simp [boundary])) hfactor
  obtain ⟨result,hvalid,hinit,_,hresult⟩ := separator_context hs.tokens_valid hs.initial hd
    Symbol.club Symbol.spade (by simp [boundary]) (Or.inr rfl) (Or.inr (by decide))
    (ending s.outer) pre' (us ++ vs) post
    (ending_boundary_free _ Symbol.club (by simp [boundary]))
    (ending_boundary_free _ Symbol.spade (by simp [boundary]))
    (by simpa [List.append_assoc] using hrest)
  have hout : pre ++ (Symbol.club :: us) ++ z ++ (vs ++ [Symbol.spade]) ++ post =
      left s ++ encode result ++ ending s.outer := by
    calc
      _ = pre ++ y ++ post := by simp [ey,List.append_assoc]
      _ = left s ++ (pre' ++ encode donor ++ post) := by simp [hpre,hyshape,List.append_assoc]
      _ = _ := by rw [hresult]; simp [List.append_assoc]
  apply finish_right s hs hword pre (Symbol.club :: us) (vs ++ [Symbol.spade]) post z ex result hvalid hinit _ hout
  intro hf
  have hm : Symbol.club ∈ x := by rw [ex]; simp
  exact (unframed_no_club hs hf (hword ▸ hm)).elim

private theorem left_no_diamond (s : State) : diamond ∉ left s := by
  cases hj : s.j with
  | none => cases s.outer <;> simp [left,RowState.lead,hj,junctionLeft,junctionRight,punctuation,h]
  | some p => cases p <;> cases s.outer <;>
      simp [left,RowState.lead,hj,junctionLeft,junctionRight,punctuation,phaseLeft,phaseRight,h]

/-- Cp-to-diamond donors replace a suffix through the unique outer endpoint. -/
theorem diamond_closed {x y : Word} (hi : Invariant x) (hy : Closure seeds y)
    (hyend : FiniteCases.ends y = (some Cp,some diamond))
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨s,hs,hword⟩ := hi
  obtain ⟨donor,hd,hdi,hyshape⟩ := diamond_tokens hy hyend
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends Cp diamond y u z v hu hv ey hyend
  have houter : s.outer = true := by
    cases hf : s.outer with
    | true => rfl
    | false =>
      have hm : diamond ∈ word s := by rw [← hword,ex]; simp
      have hn : diamond ∉ word s := by
        rw [word_eq]
        simp [left_no_diamond,encode_no_diamond hs.tokens_valid,ending,hf]
      exact (hn hm).elim
  have hfactor : left s ++ (encode s.tokens ++ [natural,diamond]) =
      pre ++ Cp :: (us ++ vs ++ diamond :: post) := by
    simpa [word_eq,ending,houter,List.append_assoc] using hword.symm.trans ex
  obtain ⟨pre',hpre,hrest⟩ := after_free Cp (left s) (encode s.tokens ++ [natural,diamond])
    pre _ (left_free s Cp (by simp [boundary])) hfactor
  obtain ⟨result,hvalid,hinit,hresult⟩ := replace_terminal hs.tokens_valid hs.initial hd hdi
    pre' (us ++ vs) post (by simpa [List.append_assoc] using hrest)
  have hout : pre ++ (Cp :: us) ++ z ++ (vs ++ [diamond]) ++ post =
      left s ++ encode result ++ ending s.outer := by
    calc
      _ = pre ++ y ++ post := by simp [ey,List.append_assoc]
      _ = left s ++ (pre' ++ encode donor ++ [natural,diamond] ++ post) := by
        simp [hpre,hyshape,List.append_assoc]
      _ = _ := by rw [hresult]; simp [ending,houter,List.append_assoc]
  exact finish_right s hs hword pre (Cp :: us) (vs ++ [diamond]) post z ex result hvalid hinit
    (by simp [houter]) hout

end TokenState

end

/- ================= PARSING RETAINED ROWS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens
namespace TokenState

def outerMark (outer : Bool) : Word := if outer then [heart] else []
def rowCode (rows : List (List Letter)) : Word :=
  BlockBoundaries.encode dollar sharp (rows.map h)

theorem rowCode_append (a b : List (List Letter)) : rowCode (a ++ b) = rowCode a ++ rowCode b := by
  simp [rowCode,BlockBoundaries.encode,List.flatMap_append]

theorem lead_rotate (outer : Bool) (rows : List (List Letter)) :
    RowState.lead outer rows = outerMark outer ++ rowCode rows ++ [dollar] := by
  have aux : [dollar] ++ rows.flatMap (fun a => h a ++ [sharp,dollar]) = rowCode rows ++ [dollar] := by
    induction rows with
    | nil => rfl
    | cons a rows ih =>
      simpa [rowCode,BlockBoundaries.encode,List.flatMap_map,List.append_assoc] using
        congrArg (fun w => [dollar] ++ h a ++ [sharp] ++ w) ih
  simpa [RowState.lead,outerMark,List.append_assoc] using
    congrArg (fun w => outerMark outer ++ w) aux

theorem encode_rank3 {ts : List Token} (hv : AllValid ts) (a : Symbol) (ha : a ∈ encode ts) :
    LocalSyntax.rank a = 3 := by
  obtain ⟨t,ht,ha⟩ := List.mem_flatMap.mp ha
  have hv' := hv t ht
  cases t with
  | club =>
    have he : a = Symbol.club := by simpa [code,start,interior] using ha
    subst a; rfl
  | spade =>
    have he : a = Symbol.spade := by simpa [code,start,interior] using ha
    subst a; rfl
  | block r =>
    simp only [code,start,interior,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | ha | rfl
    · rfl
    · have hr := hv'.1 a ha
      cases a <;> simp_all [RightStructure.rawSymbol,LocalSyntax.rank]
    · rfl

theorem encode_no_core {ts : List Token} (hv : AllValid ts) (a : Symbol) (ha : LocalSyntax.rank a ≠ 3) :
    a ∉ encode ts := fun hm => ha (encode_rank3 hv a hm)

def restRows (s : State) : Word := [flat] ++ junctionRight s.j ++ encode s.tokens ++ ending s.outer

theorem rest_no_dollar {s : State} (hs : Valid s) : dollar ∉ restRows s := by
  have he := encode_no_core hs.tokens_valid dollar (by decide)
  cases hj : s.j with
  | none => cases s.outer <;> simp [restRows,hj,junctionRight,ending,he]
  | some p => cases p <;> cases s.outer <;> simp [restRows,hj,junctionRight,phaseRight,ending,he]

theorem row_form (s : State) : word s = outerMark s.outer ++
    BlockBoundaries.encode dollar sharp (s.prior.map h ++ [h s.last ++ junctionLeft s.j]) ++
    (if s.j.isNone then [dollar] else []) ++ restRows s := by
  rw [word_eq]
  unfold left
  rw [lead_rotate]
  cases hj : s.j <;>
    simp [rowCode,BlockBoundaries.encode,restRows,hj,junctionLeft,punctuation,
      List.flatMap_append,List.flatMap_map,List.append_assoc]

private theorem proper_map_prefix {α β : Type} (f : α → β) (as : List α) (last : β)
    (left : List β) (p : β) (right : List β) (he : as.map f ++ [last] = left ++ p :: right) :
    ∃ rs rest, as = rs ++ rest ∧ left = rs.map f := by
  induction as generalizing left with
  | nil =>
    cases left with
    | nil => exact ⟨[],[],rfl,rfl⟩
    | cons b left =>
      have hl := congrArg List.length he
      simp at hl
  | cons a as ih =>
    cases left with
    | nil => exact ⟨[],a :: as,rfl,rfl⟩
    | cons b left =>
      have hb : f a = b := (List.cons.inj he).1
      obtain ⟨rs,rest,has,hleft⟩ := ih left (List.cons.inj he).2
      exact ⟨a :: rs,rest,by simp [has],by simp [hb,hleft]⟩

private theorem final_dollar_prefix (rows : List (List Letter)) (rest pre tail : Word)
    (hn : dollar ∉ rest) (he : rowCode rows ++ dollar :: rest = pre ++ dollar :: tail) :
    ∃ rs remaining, rows = rs ++ remaining ∧ pre = rowCode rs := by
  induction rows generalizing pre with
  | nil =>
    cases pre with
    | nil => exact ⟨[],[],rfl,rfl⟩
    | cons b pre =>
      have hr : rest = pre ++ dollar :: tail := (List.cons.inj he).2
      exact (hn (by rw [hr]; simp)).elim
  | cons r rows ih =>
    cases pre with
    | nil => exact ⟨[],r :: rows,rfl,rfl⟩
    | cons b pre =>
      have hb : dollar = b := (List.cons.inj he).1
      have hr : (h r ++ [sharp]) ++ (rowCode rows ++ dollar :: rest) = pre ++ dollar :: tail := by
        simpa [rowCode,BlockBoundaries.encode,List.flatMap_map,List.append_assoc] using (List.cons.inj he).2
      obtain ⟨q,hq,hrest⟩ := after_free dollar (h r ++ [sharp]) (rowCode rows ++ dollar :: rest)
        pre tail (by simp [h]) hr
      obtain ⟨rs,remaining,hrows,hpre⟩ := ih q hrest
      exact ⟨r :: rs,remaining,by simp [hrows],by
        simp [rowCode,BlockBoundaries.encode,hb,hq,hpre,List.append_assoc]⟩

/-- A dollar-anchor always retains a prefix of complete left rows. -/
theorem dollar_prefix {s : State} (hs : Valid s) (pre rest : Word)
    (he : word s = pre ++ dollar :: rest) :
    ∃ rs, pre = outerMark s.outer ++ rowCode rs ∧
      (∀ r ∈ rs, r ∈ s.prior ++ [s.last]) := by
  have houter : dollar ∉ outerMark s.outer := by cases s.outer <;> decide
  cases hj : s.j with
  | some p =>
    have hf : word s = outerMark s.outer ++
        (BlockBoundaries.encode dollar sharp (s.prior.map h ++ [h s.last ++ phaseLeft p]) ++ restRows s) := by
      simpa [hj,junctionLeft,List.append_assoc] using row_form s
    obtain ⟨q,hq,hrest⟩ := after_free dollar (outerMark s.outer) _ pre rest houter (hf.symm.trans he)
    have hn : ∀ t ∈ s.prior.map h ++ [h s.last ++ phaseLeft p], dollar ∉ t := by
      intro t ht
      simp only [List.mem_append,List.mem_map,List.mem_singleton] at ht
      rcases ht with ⟨r,_,rfl⟩ | rfl
      · simp [h]
      · cases p <;> simp [h,phaseLeft]
    obtain ⟨left,t,right,hrows,hpre,_⟩ := BlockBoundaries.prefix_exact dollar sharp
      (s.prior.map h ++ [h s.last ++ phaseLeft p]) (restRows s) (by decide) hn (rest_no_dollar hs)
      q rest hrest
    obtain ⟨rs,remaining,hprior,hleft⟩ := proper_map_prefix h s.prior _ left t right hrows
    refine ⟨rs,by simp [hq,hpre,hleft,rowCode],?_⟩
    intro r hr
    exact List.mem_append_left _ (by rw [hprior]; exact List.mem_append_left _ hr)
  | none =>
    have hf : word s = outerMark s.outer ++ (rowCode (s.prior ++ [s.last]) ++ dollar :: restRows s) := by
      simpa [hj,junctionLeft,rowCode,BlockBoundaries.encode,List.flatMap_append,List.append_assoc] using row_form s
    obtain ⟨q,hq,hrest⟩ := after_free dollar (outerMark s.outer) _ pre rest houter (hf.symm.trans he)
    obtain ⟨rs,remaining,hrows,hpre⟩ := final_dollar_prefix (s.prior ++ [s.last]) (restRows s)
      q rest (rest_no_dollar hs) hrest
    refine ⟨rs,by simp [hq,hpre],?_⟩
    intro r hr
    rw [hrows]
    exact List.mem_append_left _ hr

end TokenState

end

/- ================= CORE SPLICE LEMMAS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens
namespace TokenState

theorem word_head (s : State) : (word s).head? = some (if s.outer then heart else dollar) := by
  cases ho : s.outer <;> simp [word,junctionBody,RowState.lead,ho]

theorem core_outer {s : State} (he : FiniteCases.ends (word s) = (some dollar,some natural)) :
    s.outer = false := by
  have hh := congrArg Prod.fst he
  cases ho : s.outer <;> simp_all [FiniteCases.ends,word_head]

theorem left_no_natural (s : State) : natural ∉ left s := by
  cases hj : s.j with
  | none => cases s.outer <;> simp [left,RowState.lead,hj,junctionLeft,junctionRight,punctuation,h]
  | some p => cases p <;> cases s.outer <;>
      simp [left,RowState.lead,hj,junctionLeft,junctionRight,punctuation,phaseLeft,phaseRight,h]

/-- In a word with one delimiter, both surrounding contexts are fixed. -/
theorem unique_occurrence (a : Symbol) (front trail pre post : Word)
    (hf : a ∉ front) (ht : a ∉ trail) (he : front ++ a :: trail = pre ++ a :: post) :
    pre = front ∧ post = trail := by
  obtain ⟨q,hq,hr⟩ := after_free a front (a :: trail) pre post hf he
  cases q with
  | nil => exact ⟨by simpa using hq,by simpa using (List.cons.inj hr).2.symm⟩
  | cons b q =>
    have hb : a = b := (List.cons.inj hr).1
    have hm : a ∈ trail := by rw [(List.cons.inj hr).2]; simp
    exact (ht hm).elim

theorem natural_suffix {s : State} (hs : Valid s) (pre post : Word)
    (he : word s = pre ++ natural :: post) : post = if s.outer then [diamond] else [] := by
  have hf : natural ∉ left s ++ encode s.tokens := by
    simp [left_no_natural,encode_no_core hs.tokens_valid natural (by decide)]
  exact (unique_occurrence natural (left s ++ encode s.tokens)
    (if s.outer then [diamond] else []) pre post hf
    (by cases s.outer <;> decide)
    (by simpa [word_eq,ending,List.append_assoc] using he)).2

theorem simple_as_singletons {ts : List Token} (hs : Simple ts) :
    ∃ beta, ts = singletonTokens beta := by
  induction ts with
  | nil => exact ⟨[],rfl⟩
  | cons t ts ih =>
    obtain ⟨a,rfl⟩ := hs t (by simp)
    obtain ⟨beta,hb⟩ := ih (fun t ht => hs t (by simp [ht]))
    exact ⟨beta ++ [a],by simp [singletonTokens,hb,List.reverse_append]⟩

theorem simple_unique {ts : List Token} (hs : Simple ts) {v w : List Letter}
    (hv : Soundness.Chooses (blockLists ts).reverse v)
    (hw : Soundness.Chooses (blockLists ts).reverse w) : v = w := by
  obtain ⟨beta,rfl⟩ := simple_as_singletons hs
  have forced : ∀ {v : List Letter}, Soundness.Chooses (beta.map (fun a => [a])) v → v = beta := by
    clear hs hv hw
    intro v hv
    induction beta generalizing v with
    | nil => cases hv; rfl
    | cons a beta ih =>
      cases hv with
      | cons ha h =>
        have he := List.mem_singleton.mp ha
        simp [he,ih h]
  have hv' : Soundness.Chooses (beta.map (fun a => [a])) v := by
    simpa [singleton_blocks,← List.map_reverse] using hv
  have hw' : Soundness.Chooses (beta.map (fun a => [a])) w := by
    simpa [singleton_blocks,← List.map_reverse] using hw
  exact (forced hv').trans (forced hw').symm

theorem initial_shape {ts : List Token} (hi : Initial ts) : ∃ rest, encode ts = Cp :: rest := by
  obtain ⟨a,rest,rfl⟩ := hi
  exact ⟨Bp a :: Ap :: encode rest,rfl⟩

/-- Retaining the whole physical tail in a core donor is sufficient for
semantic preservation; all new concrete blocks share one forced witness. -/
theorem core_tail_embedding {old : State} (ho : Valid old) {donor : State}
    (hd : Valid donor) (hout : donor.outer = false)
    (he : (encode old.tokens).Sublist (word donor)) :
    (encode old.tokens).Sublist (encode donor.tokens) := by
  obtain ⟨rest,hr⟩ := initial_shape ho.initial
  have hword : word donor = left donor ++ (encode donor.tokens ++ [natural]) := by
    simp [word_eq,ending,hout,List.append_assoc]
  rw [hword,hr] at he
  have hskip := Soundness.skip_marker_free Cp (left donor) rest (encode donor.tokens ++ [natural])
    (left_free donor Cp (by simp [boundary])) he
  have hs : (encode old.tokens).Sublist (encode donor.tokens ++ [natural]) := by simpa [hr] using hskip
  apply hs.of_sublist_append_left
  intro a ha hm
  have hnat : a = natural := by simpa using hm
  subst a
  exact encode_no_core ho.tokens_valid natural (by decide) ha

/-- A host tail starts after any retained complete left-row prefix. -/
theorem host_tail_in_anchors {s : State} (hs : Valid s)
    (pre u v post : Word) (he : word s = pre ++ u ++ v ++ post)
    (hp : Cp ∉ pre) (hpost : ∀ a ∈ post, LocalSyntax.rank a ≠ 3) :
    (encode s.tokens).Sublist (u ++ v) := by
  have ht : (encode s.tokens).Sublist (word s) := by
    rw [word_eq]
    exact (List.sublist_append_right (left s) (encode s.tokens)).trans (List.sublist_append_left _ _)
  obtain ⟨rest,hr⟩ := initial_shape hs.initial
  rw [he,hr] at ht
  have hskip := Soundness.skip_marker_free Cp pre rest ((u ++ v) ++ post) hp
    (by simpa [List.append_assoc] using ht)
  have ht' : (encode s.tokens).Sublist ((u ++ v) ++ post) := by simpa [hr] using hskip
  apply ht'.of_sublist_append_left
  intro a ha hm
  exact hpost a hm (encode_rank3 hs.tokens_valid a ha)

/-- Concatenating a complete row prefix with an unframed donor adds exactly
those rows, while retaining the host's outer frame. -/
theorem row_splice_word (donor : State) (hout : donor.outer = false)
    (outer : Bool) (rows : List (List Letter)) :
    outerMark outer ++ rowCode rows ++ word donor ++ (if outer then [diamond] else []) =
      word {donor with outer := outer, prior := rows ++ donor.prior} := by
  simp only [word_eq,left]
  rw [lead_rotate,lead_rotate]
  simp [hout,outerMark,rowCode_append,ending,List.append_assoc]

end TokenState

end

/- ================= LONG ROW-DONOR PRESERVATION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens
namespace TokenState

/-- The long row-bearing donor case. The donor's concrete tail extends one
old common witness; uniqueness of that concrete witness joins both row sets. -/
theorem core_closed {x y : Word} (hi : Invariant x) (hy : Invariant y)
    (hyend : FiniteCases.ends y = (some dollar,some natural))
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨s,hs,hword⟩ := hi
  obtain ⟨d,hd,hdword⟩ := hy
  have houter : d.outer = false := core_outer (by rw [← hdword]; exact hyend)
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends dollar natural y u z v hu hv ey hyend
  obtain ⟨rs,hpre,hrs⟩ := dollar_prefix hs pre (us ++ vs ++ natural :: post)
    (by simpa [List.append_assoc] using hword.symm.trans ex)
  have hpost : post = if s.outer then [diamond] else [] := natural_suffix hs
    (pre ++ dollar :: us ++ vs) post
    (by simpa [List.append_assoc] using hword.symm.trans ex)
  have hpcp : Cp ∉ pre := by
    rw [hpre]
    cases s.outer <;> simp [outerMark,rowCode,BlockBoundaries.encode,h]
  have hpRank : ∀ a ∈ post, LocalSyntax.rank a ≠ 3 := by
    rw [hpost]
    cases s.outer <;> simp [LocalSyntax.rank]
  have ht := host_tail_in_anchors hs pre (dollar :: us) (vs ++ [natural]) post
    (hword.symm.trans ex) hpcp hpRank
  have huv : ((dollar :: us) ++ (vs ++ [natural])).Sublist y := by
    rw [ey]
    simpa [List.append_assoc] using
      (List.sublist_append_right z (vs ++ [natural])).append_left (dollar :: us)
  have htail : (encode s.tokens).Sublist (encode d.tokens) :=
    core_tail_embedding hs hd houter (by simpa [hdword] using ht.trans huv)
  obtain ⟨oldWitness,how,hor⟩ := good_monotone hs.tokens_valid hd.tokens_valid htail hs.good
  obtain ⟨w,hw,hdr⟩ := hd.good
  have hew : oldWitness = w := simple_unique (hd.simple houter) how hw
  subst oldWitness
  let result : State := {d with outer := s.outer, prior := rs ++ d.prior}
  have hrne : ∀ r ∈ rs, r ≠ [] := by
    intro r hr
    rcases List.mem_append.mp (hrs r hr) with hm | hm
    · exact hs.prior_ne r hm
    · have he := List.mem_singleton.mp hm
      simpa [he] using hs.last_ne
  have hvalid : Valid result := by
    refine ⟨hd.last_ne,?_,hd.tokens_valid,hd.initial,?_,?_⟩
    · intro r hr
      exact (List.mem_append.mp hr).elim (hrne r) (hd.prior_ne r)
    · intro _
      exact hd.simple houter
    · refine ⟨w,hw,?_⟩
      intro r hr
      have hm : r ∈ rs ∨ r ∈ d.prior ∨ r = d.last := by
        simpa [result,List.mem_append,or_assoc] using hr
      rcases hm with hm | hm | rfl
      · exact hor r (hrs r hm)
      · exact hdr r (List.mem_append_left _ hm)
      · exact hdr d.last (by simp)
  refine ⟨result,hvalid,?_⟩
  calc
    _ = pre ++ y ++ post := by simp [ey,List.append_assoc]
    _ = outerMark s.outer ++ rowCode rs ++ word d ++ (if s.outer then [diamond] else []) := by
      simp [hpre,hdword,hpost,List.append_assoc]
    _ = word result := row_splice_word d houter s.outer rs

end TokenState

end

/- ================= SEEDS AND EXHAUSTIVE ENDPOINT CLASSIFICATION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens FiniteCases LocalSyntax
namespace TokenState

def envelope : Word := [heart,dollar,natural,diamond]
def MainInvariant (w : Word) : Prop := w = envelope ∨ Invariant w

theorem insertion_ends (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ []) :
    ends (pre ++ u ++ z ++ v ++ post) = ends (pre ++ u ++ v ++ post) := by
  apply Prod.ext
  · cases pre <;> cases u <;> simp_all [ends]
  · have hv' : v.getLast? ≠ none := by simpa using hv
    cases hp : post.getLast? with
    | some a => simp [ends,List.getLast?_append,hp]
    | none =>
      cases he : v.getLast? with
      | none => exact (hv' he).elim
      | some a => simp [ends,List.getLast?_append,hp,he]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem seed_end_check : ∀ w ∈ seeds, allEnd (ends w) = true := by decide +kernel

theorem generated_end_check {w : Word} (hw : Closure seeds w) : allEnd (ends w) = true := by
  obtain ⟨v,hv,he⟩ := List.mem_map.mp (closure_ends hw)
  rw [← he]
  exact seed_end_check v hv

theorem endpoint_cases {w : Word} (hw : Closure seeds w) :
    ends w = (some dollar,some natural) ∨ ends w = (some heart,some diamond) ∨
    ends w = (some Cp,some Cp) ∨ ends w = (some Cp,some Symbol.club) ∨
    ends w = (some Cp,some diamond) ∨ smallEnd (ends w) = true := by
  have he := generated_end_check hw
  generalize hp : ends w = p at he ⊢
  rcases p with ⟨a,b⟩
  cases a with
  | none => simp [allEnd,smallEnd] at he
  | some a =>
    cases b with
    | none => cases a <;> simp [allEnd,smallEnd] at he
    | some b => cases a <;> cases b <;> simp_all [allEnd,smallEnd]

theorem short_cases {w : Word} (hw : w ∈ small) :
    (∃ e, w ∈ Completion.donors e) ∨ (∃ a b, w = bridge a b) ∨
      ends w = (some Symbol.club,some Symbol.spade) := by
  simp only [small,List.mem_append,List.mem_flatMap,List.mem_map] at hw
  rcases hw with ⟨a,_,ha⟩ | hm
  · rcases ha with ha | ⟨b,_,hb⟩
    · exact Or.inl ⟨a,ha⟩
    · exact Or.inr (Or.inl ⟨a,b,hb.symm⟩)
  · obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
    right; right
    rw [← hi]
    simp [ends,List.getLast?_append,List.getLast?_cons]

/-- Outer endpoints force a complete replacement in every generated host. -/
theorem framed_whole {x y : Word} (hx : Closure seeds x)
    (hyend : ends y = (some heart,some diamond))
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    pre ++ u ++ z ++ v ++ post = y := by
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends heart diamond y u z v hu hv ey hyend
  have ho := closure_ordered hx
  rw [ex] at ho
  have hp : pre = [] := by
    cases pre with
    | nil => rfl
    | cons a pre =>
      have ho' : ((a :: pre) ++ ((heart :: us) ++ (vs ++ [diamond]) ++ post)).Pairwise ordered := by
        simpa [List.append_assoc] using ho
      have hh := (List.pairwise_append.mp ho').2.2 a (by simp) heart (by simp)
      cases a <;> simp [ordered,rank] at hh
  have ht : post = [] := by
    cases post with
    | nil => rfl
    | cons b post =>
      have hh := (List.pairwise_append.mp ho).2.2 diamond (by simp) b (by simp)
      cases b <;> simp [ordered,rank] at hh
  simp [hp,ht,ey,List.append_assoc]

def seedBetas (a : Letter) : List (List Letter) := [[a]] ++ letters.flatMap fun b => [[a,b],[b,a]]
def coreWord (a : Letter) (beta : List Letter) : Word := [dollar] ++ h [a] ++ [sharp,flat] ++ hr beta ++ [natural]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem row_seed_check : ∀ w ∈ seeds,
    (ends w = (some dollar,some natural) ∨ ends w = (some heart,some diamond)) →
    w = envelope ∨ ∃ a ∈ letters, ∃ beta ∈ seedBetas a, w = coreWord a beta := by decide +kernel
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem seed_beta_check : ∀ a ∈ letters, ∀ beta ∈ seedBetas a, a ∈ beta ∧ beta ≠ [] := by decide +kernel

theorem core_seed (a : Letter) (beta : List Letter) (ha : a ∈ beta) (hb : beta ≠ []) :
    Invariant (coreWord a beta) := by
  let s : State := ⟨false,[],[a],some .ready,singletonTokens beta⟩
  have hg : Soundness.Good [[a]] beta [] := by
    refine ⟨[],.nil,?_⟩
    intro r hr
    have he := List.mem_singleton.mp hr
    subst r
    exact List.singleton_sublist.mpr ha
  refine ⟨s,⟨by simp [s],by simp [s],singletons_valid beta,singletons_initial hb,
    fun _ => singleton_simple beta,by simpa [s] using good_concrete (ts := []) hg⟩,?_⟩
  simp [word,s,coreWord,junctionBody,RowState.lead,junctionLeft,junctionRight,punctuation,
    phaseLeft,phaseRight,encode_singletons,ending,hr,List.append_assoc]

theorem seed_rows {w : Word} (hw : w ∈ seeds)
    (he : ends w = (some dollar,some natural) ∨ ends w = (some heart,some diamond)) : MainInvariant w := by
  rcases row_seed_check w hw he with h | ⟨a,ha,beta,hb,rfl⟩
  · exact Or.inl h
  · exact Or.inr (core_seed a beta (seed_beta_check a ha beta hb).1 (seed_beta_check a ha beta hb).2)

end TokenState

end

/- ================= OUTER ENVELOPE ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens FiniteCases
namespace TokenState
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem envelope_filter : ∀ p ∈ pairs envelope, allEnd p = true →
    p = (some dollar,some natural) ∨ p = (some heart,some diamond) := by decide +kernel

theorem envelope_donor {x y : Word} (hx : x = envelope) (hy : Closure seeds y)
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    ends y = (some dollar,some natural) ∨ ends y = (some heart,some diamond) := by
  have hp := donor_ends_pair pre u v post z hu hv
  rw [← ey,← ex,hx] at hp
  exact envelope_filter _ hp (generated_end_check hy)

/-- Inserting a core into the small outer envelope adds only its frame. -/
theorem envelope_core {x y : Word} (hx : x = envelope) (hy : Invariant y)
    (hyend : ends y = (some dollar,some natural))
    (pre u v post z : Word) (hu : u ≠ []) (hv : v ≠ [])
    (ex : x = pre ++ u ++ v ++ post) (ey : y = u ++ z ++ v) :
    Invariant (pre ++ u ++ z ++ v ++ post) := by
  obtain ⟨d,hd,hword⟩ := hy
  have hout : d.outer = false := core_outer (by rw [← hword]; exact hyend)
  obtain ⟨us,vs,rfl,rfl⟩ := RightStructure.anchor_ends dollar natural y u z v hu hv ey hyend
  have hpre : pre = [heart] := (unique_occurrence dollar [heart] [natural,diamond]
    pre (us ++ vs ++ natural :: post) (by simp) (by simp)
    (by simpa [hx,envelope,List.append_assoc] using ex)).1
  have hpost : post = [diamond] := (unique_occurrence natural [heart,dollar] [diamond]
    (pre ++ dollar :: us ++ vs) post (by simp) (by simp)
    (by simpa [hx,envelope,List.append_assoc] using ex)).2
  let result : State := {d with outer := true}
  refine ⟨result,⟨hd.last_ne,hd.prior_ne,hd.tokens_valid,hd.initial,?_,hd.good⟩,?_⟩
  · intro hf
    simp [result] at hf
  · calc
      _ = pre ++ y ++ post := by simp [ey,List.append_assoc]
      _ = [heart] ++ word d ++ [diamond] := by rw [hpre,hpost,hword]
      _ = word result := by
        simpa [outerMark,rowCode,BlockBoundaries.encode,result] using row_splice_word d hout true []
end TokenState

end

/- ================= FULL CLOSURE INDUCTION ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens FiniteCases
namespace TokenState

/-- The full closure induction. Endpoint classification covers all generated
donors; each preservation lemma covers arbitrary anchor cuts and word lengths.
This replaces the paper's explicit 13-by-13 table by grouped cases. -/
theorem generated_rows {w : Word} (hw : Closure seeds w) :
    (ends w = (some dollar,some natural) ∨ ends w = (some heart,some diamond)) → MainInvariant w := by
  induction hw with
  | seed hw => exact seed_rows hw
  | @insert x y pre post u v z hx hy hu hv ex ey ihx ihy =>
    intro he
    rw [insertion_ends pre u v post z hu hv] at he
    have hxe : ends x = (some dollar,some natural) ∨ ends x = (some heart,some diamond) := by
      rw [ex]; exact he
    rcases ihx hxe with henv | hrow
    · rcases envelope_donor henv hy pre u v post z hu hv ex ey with hcore | hframe
      · rcases ihy (Or.inl hcore) with henvy | hiy
        · simp [henvy,envelope,ends] at hcore
        · exact Or.inr (envelope_core henv hiy hcore pre u v post z hu hv ex ey)
      · rw [framed_whole hx hframe pre u v post z hu hv ex ey]
        exact ihy (Or.inr hframe)
    · rcases endpoint_cases hy with hcore | hframe | hone | hclub | hdiamond | hshort
      · rcases ihy (Or.inl hcore) with henvy | hiy
        · simp [henvy,envelope,ends] at hcore
        · exact Or.inr (core_closed hrow hiy hcore pre u v post z hu hv ex ey)
      · rw [framed_whole hx hframe pre u v post z hu hv ex ey]
        exact ihy (Or.inr hframe)
      · exact Or.inr (type_one_closed hrow hy hone pre u v post z hu hv ex ey)
      · exact Or.inr (club_closed hrow hy hclub pre u v post z hu hv ex ey)
      · exact Or.inr (diamond_closed hrow hy hdiamond pre u v post z hu hv ex ey)
      · rcases short_cases (generated_small hy hshort) with ⟨e,he⟩ | ⟨a,b,he⟩ | he
        · exact Or.inr (phase_closed hx hrow e he pre u v post z hu hv ex ey)
        · exact Or.inr (bridge_closed hx hrow a b he pre u v post z hu hv ex ey)
        · exact Or.inr (mask_closed hrow hy he pre u v post z hu hv ex ey)

end TokenState

end

/- ================= TARGET READOUT AND FINAL REDUCTION THEOREMS ================= -/
section
open SupersequenceReduction SupersequenceReduction.Symbol PhaseCases TailTokens Soundness FiniteCases
namespace TokenState

private theorem h_count (r : List Letter) (a : Symbol) (ha : a = dollar ∨ a = sharp) : (h r).count a = 0 := by
  apply List.count_eq_zero_of_not_mem
  rcases ha with rfl | rfl <;> simp [h]

private theorem row_count (rows : List (List Letter)) (a : Symbol) (ha : a = dollar ∨ a = sharp) :
    (rowCode rows).count a = rows.length := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    have he : rowCode (r :: rows) = [dollar] ++ h r ++ [sharp] ++ rowCode rows := by
      simp [rowCode,BlockBoundaries.encode,List.append_assoc]
    rw [he]
    rcases ha with rfl | rfl <;> simp [h_count,ih,List.count_cons,Nat.add_comm]

private theorem word_counts (s : State) (hs : Valid s) :
    (word s).count dollar = s.prior.length + 1 + (if s.j.isNone then 1 else 0) ∧
    (word s).count sharp = s.prior.length + 1 := by
  have hd := List.count_eq_zero_of_not_mem (encode_no_core hs.tokens_valid dollar (by decide))
  have hh := List.count_eq_zero_of_not_mem (encode_no_core hs.tokens_valid sharp (by decide))
  rw [word_eq]
  unfold left
  rw [lead_rotate]
  cases hj : s.j with
  | none => cases ho : s.outer <;>
      simp [outerMark,hj,junctionLeft,junctionRight,punctuation,ending,ho,
        hd,hh,h_count,row_count,List.count_cons,Nat.add_assoc]
  | some p => cases p <;> cases ho : s.outer <;>
      simp [outerMark,hj,junctionLeft,junctionRight,punctuation,phaseLeft,phaseRight,ending,ho,
        hd,hh,h_count,row_count,List.count_cons,Nat.add_assoc]

private theorem frame_count (rows : List (List Letter)) (beta : List Letter) (bs : List Block)
    (a : Symbol) (ha : a = dollar ∨ a = sharp) :
    (frame rows beta bs).count a = rows.length + (if a = dollar then 1 else 0) := by
  let rest := [flat] ++ hr beta ++ bs.reverse.flatMap (fun b => [Symbol.spade,Symbol.club] ++ block b) ++
    [Symbol.spade,Symbol.club,natural,diamond]
  have hb : ∀ b : Block, a ∉ block b := by
    intro b
    cases b with
    | none => rcases ha with rfl | rfl <;> decide +kernel
    | some c => rcases ha with rfl | rfl <;> simp [block]
  have hn : a ∉ rest := by
    rcases ha with rfl | rfl <;> simp [rest,hr,hb]
  have he : frame rows beta bs = RowState.lead true rows ++ rest := by
    simp [frame,RowState.lead,rest,List.append_assoc]
  rw [he,List.count_append,List.count_eq_zero_of_not_mem hn,lead_rotate]
  rcases ha with rfl | rfl <;> simp [outerMark,row_count,List.count_cons]

private theorem target_completed {s : State} (hs : Valid s) (i : Instance) (he : reduce i = word s) :
    s.j = none := by
  have hb : (word s).count dollar = (word s).count sharp + 1 := by
    rw [← he]
    simp only [reduce,frame_count _ _ _ dollar (Or.inl rfl),frame_count _ _ _ sharp (Or.inr rfl)]
    simp
  rw [(word_counts s hs).1,(word_counts s hs).2] at hb
  cases hj : s.j with
  | none => rfl
  | some p => simp [hj] at hb

private theorem encoded_rows_empty {ts : List Token} (hv : AllValid ts) :
    (encode ts).filterMap rowToken = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro a ha
  have hr := encode_rank3 hv a ha
  cases a <;> simp_all [LocalSyntax.rank,rowToken]

private theorem rowCode_projection (rows : List (List Letter)) :
    (rowCode rows).filterMap rowToken = packed rows := by
  have he := congrArg (List.filterMap rowToken) (lead_rotate false rows)
  simpa [RowState.lead,outerMark,List.filterMap_append,rowToken,Soundness.row_projection] using he.symm

private theorem word_row_projection {s : State} (hs : Valid s) (hj : s.j = none) :
    (word s).filterMap rowToken = packed (s.prior ++ [s.last]) := by
  have he : word s = outerMark s.outer ++ rowCode (s.prior ++ [s.last]) ++ [dollar] ++ restRows s := by
    simpa [hj,junctionLeft,rowCode,BlockBoundaries.encode,List.flatMap_append,List.append_assoc] using row_form s
  rw [he]
  have hrest : (restRows s).filterMap rowToken = [] := by
    cases ho : s.outer <;> simp [restRows,hj,junctionRight,List.filterMap_append,
      encoded_rows_empty hs.tokens_valid,ending,ho,rowToken]
  cases ho : s.outer <;> simp [List.filterMap_append,outerMark,ho,rowCode_projection,rowToken,hrest]

private theorem word_right_projection {s : State} (hs : Valid s) (hj : s.j = none) :
    (word s).filterMap rightProjection = packed (blockLists s.tokens) := by
  have hl : (left s).filterMap rightProjection = [] := by
    cases ho : s.outer <;> simp [left,RowState.lead,h,hj,junctionLeft,junctionRight,punctuation,
      ho,List.filterMap_append,List.filterMap_flatMap,rightProjection]
  rw [word_eq,List.filterMap_append,List.filterMap_append,hl,projection hs.tokens_valid]
  cases ho : s.outer <;> simp [ending,ho,rightProjection]

/-- The invariant on the literal target yields exactly the original SCS instance. -/
theorem invariant_target_sound (i : Instance) (hi : Invariant (reduce i)) : SCS i := by
  obtain ⟨s,hs,hword⟩ := hi
  have hj := target_completed hs i hword
  have hrows : s.prior ++ [s.last] = markedRows i := by
    apply packed_injective
    have he := congrArg (List.filterMap rowToken) hword
    simpa [reduce,frame_rows,word_row_projection hs hj] using he.symm
  have hblocks : blockLists s.tokens = [[none]] ++ List.replicate i.p letters := by
    apply packed_injective
    have he := congrArg (List.filterMap rightProjection) hword
    simpa [reduce,frame_projection,blockChoices,word_right_projection hs hj] using he.symm
  obtain ⟨w,hw,hr⟩ := hs.good
  have hw' : Chooses (List.replicate i.p letters ++ [[none]]) w := by
    simpa [hblocks] using hw
  obtain ⟨v,hv,rfl⟩ := chooses_last hw'
  apply target_sound i
  refine ⟨v,hv,?_⟩
  intro r hm
  simpa using hr r (by rw [hrows]; exact hm)

/-- The missing converse is unconditional: it assumes only membership in
the original insertion closure of the repaired finite seed language. -/
theorem membership_implies_scs (i : Instance) (hi : Closure seeds (reduce i)) : SCS i := by
  have he : ends (reduce i) = (some heart,some diamond) := by
    simp [ends,reduce,frame,List.getLast?_append,List.getLast?_cons]
  rcases generated_rows hi (Or.inr he) with henv | hr
  · have hm : flat ∈ reduce i := by simp [reduce,frame]
    simp [henv,envelope] at hm
  · exact invariant_target_sound i hr

end TokenState

namespace SupersequenceReduction
/-- The polynomial-time reduction is correct in both directions. -/
theorem reduction_correct (i : Instance) : SCS i ↔ Closure seeds (reduce i) :=
  ⟨Completion.scs_implies_membership i,TokenState.membership_implies_scs i⟩
theorem reduction_claim : ReductionClaim :=
  ⟨implementation_certificate.1,reduction_correct,implementation_certificate.2⟩
#print axioms reduction_correct
#print axioms reduction_claim
end SupersequenceReduction

end
