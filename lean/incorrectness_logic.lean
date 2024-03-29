
import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

import lean.language

namespace IncLogic

/-! ## Post -/
/- the def of post from the paper-/
def post (ty: IncLoLang.LogicType) (C: IncLoLang.stmt) (P: IncLoLang.state → Prop) : 
  IncLoLang.state → Prop := 
  λ σ', ∃ σ, P σ ∧ IncLoLang.lang_semantics C ty σ σ'

/-! ## Incorrectness logic and Hoare logic encodings -/

def underaproximation_triple (ty: IncLoLang.LogicType) (P: IncLoLang.prop) 
  (R: IncLoLang.stmt) (Q : IncLoLang.prop) : Prop := 
  ∀ state, Q state → post ty R P state

def overaproximation_triple (ty: IncLoLang.LogicType) (P: IncLoLang.prop) 
  (R: IncLoLang.stmt) (Q: IncLoLang.prop) : Prop := 
  ∀ state, post ty R P state → Q state



/-! ## Notation -/
notation `{* ` P : 1 ` *} ` S : 1 ` {* ` ty `:` Q : 1 ` *}` :=
  overaproximation_triple ty P S Q

notation `[* ` P : 1 ` *] ` S : 1 ` [* ` ty `:` Q : 1 ` *]` :=
  underaproximation_triple ty P S Q

example (P Q: IncLoLang.prop) (C: IncLoLang.stmt): Prop := [* P *]C[* IncLoLang.LogicType.ok: Q*]
example (P Q: IncLoLang.prop) (C: IncLoLang.stmt): Prop := {* P *}C{* IncLoLang.LogicType.ok: Q*}

/-! ## Incorrectness rules -/

/- Empty under approximates -/ 
lemma empty_under_incorrect {P C ty} : [* P *] C [* ty: λ st, false *] :=
begin
  intro state,
  finish,
end

/- Consequence-/
lemma consequence_incorrect {P Q C ty} 
  {P': IncLoLang.prop} {Q': IncLoLang.prop} 
  (h : [* P *] C [* ty: Q *]) (hQ: ∀ σ, Q' σ → Q σ) (hP: ∀ σ, P σ → P' σ):
  [* P' *] C [* ty: Q' *]:=
begin
  intros state hQ',
  specialize hQ state hQ',
  specialize h state hQ,
  rcases h with ⟨ start_state, ⟨ hP₂, lang ⟩ ⟩ ,
  use start_state,
  exact ⟨hP start_state hP₂, lang⟩,
end

/- Disjunction -/
lemma disjunction_incorrect (P₁ P₂ Q₁ Q₂ C ty) 
  (h₁ : [* P₁ *] C [* ty: Q₁ *]) 
  (h₂ : [* P₂ *] C [* ty: Q₂ *]):
  [* λ σ, P₁ σ ∨ P₂ σ *] C [* ty: λ σ, Q₁ σ ∨ Q₂ σ *] :=
begin
  intros end_state hEnd,
  cases hEnd,
  {
    specialize h₁ end_state hEnd,
    rcases h₁ with ⟨ start_state, ⟨ hP, h₁⟩ ⟩,
    use start_state,
    split,
    {
      left,
      exact hP,
    },
    { exact h₁, },
  },
  {
    specialize h₂ end_state hEnd,
    rcases h₂ with ⟨ start_state, ⟨ hP, h₂⟩ ⟩,
    use start_state,
    split,
    {
      right,
      exact hP,
    },
    { exact h₂, },
  },
end

/- Unit Ok -/
lemma unit_incorrect_ok {P} : [* P *] IncLoLang.stmt.skip [* IncLoLang.LogicType.ok: P *] :=
begin
  intros end_state hP,
  use end_state,
  split,
  { exact hP,},
  { exact IncLoLang.lang_semantics.skip, },
end

/- Sequencing short circuit -/ 
lemma seq_short_circuit_incorrect {P R S} {T: IncLoLang.stmt} (hS : [* P *] S [* IncLoLang.LogicType.er: R *] ) :
  [* P *] S ;; T [* IncLoLang.LogicType.er: R *] :=
begin
  intros end_state hStartR,
  specialize hS end_state hStartR,
  rcases hS with ⟨ start_state, ⟨ hP, hS ⟩  ⟩ ,
  use start_state,
  exact ⟨ hP, IncLoLang.lang_semantics.seq_er_1 hS⟩,
end

/- Sequencing normal -/ 
lemma seq_normal_incorrect {P R S T ty} (Q: IncLoLang.prop) 
  (hS : [* P *] S [* IncLoLang.LogicType.ok: Q *]) (hT : [* Q *] T [* ty: R *]) :
  [* P *] S ;; T [* ty: R *] :=
begin
  intros end_state hStartR,
  specialize hT end_state hStartR,
  rcases hT with ⟨ mid_state, ⟨ hMidQ, r⟩ ⟩,
  specialize hS mid_state hMidQ,
  rcases hS with ⟨ start_state, ⟨ hStartP, t⟩ ⟩,
  use start_state,
  split,
  { exact hStartP, },
  { cases ty, repeat { exact IncLoLang.lang_semantics.seq_ty t r }, },
end

/- Iterate zero -/
lemma iterate_zero_incorrect {C} (P) :
  [* P *] (C**) [* IncLoLang.LogicType.ok: P *] :=
begin
  intros state hState,
  use state,
  split,
  { exact hState, },
  { 
    have h : IncLoLang.lang_semantics (IncLoLang.repeat C 0) IncLoLang.LogicType.ok state state, {
      rw IncLoLang.repeat,
      exact IncLoLang.lang_semantics.skip,
    },
    exact IncLoLang.lang_semantics.star 0 h, 
  },
end

/- Iterate non-zero -/
lemma iterate_non_zero_incorrect {C P Q ty} (h: [* P *] C** ;; C [* ty: Q *]):
  [* P *] (C**) [* ty: Q *] :=
begin
  intros state hState,
  specialize h state hState,
  rcases h with ⟨ bState, ⟨ hBState, h ⟩ ⟩ ,
  use bState,
  split,
  { exact hBState, },
  { 
    cases h, 
    {
      cases h_H1,
      have H: IncLoLang.lang_semantics (IncLoLang.repeat C (nat.succ h_H1_i)) ty bState state, {
        rw IncLoLang.repeat,
        exact IncLoLang.lang_semantics.seq_ty (h_H1_h) (h_H2)
      },
      exact IncLoLang.lang_semantics.star (nat.succ h_H1_i) H,
    },
    { exact h_H1, },
  }
end

/- Choice left -/
lemma choice_left_incorrect {C₁ C₂ P Q ty} (h: [* P *] C₁ [* ty: Q *]):
  [* P *] (C₁ <+> C₂)  [* ty: Q *] :=
begin
  intros state hState,
  specialize h state hState,
  rcases h with ⟨ bState, ⟨ hBState, h ⟩ ⟩ ,
  use bState,
  split,
  { exact hBState, },
  { exact IncLoLang.lang_semantics.choice_left h, }
end

/- Choice right -/
lemma choice_right_incorrect {C₁ C₂ P Q ty} (h: [* P *] C₂ [* ty: Q *]):
  [* P *] (C₁ <+> C₂) [* ty: Q *] :=
begin
  intros state hState,
  specialize h state hState,
  rcases h with ⟨ bState, ⟨ hBState, h ⟩ ⟩ ,
  use bState,
  split,
  { exact hBState, },
  { exact IncLoLang.lang_semantics.choice_right h, }
end

/- Error er -/
lemma error_er_incorrect {P}:
  [* P *] (IncLoLang.stmt.error) [* IncLoLang.LogicType.er: P *] :=
begin
  intros state hState,
  use state,
  split,
  { exact hState, },
  { exact IncLoLang.lang_semantics.error, },
end

/- Assume ok -/
lemma assume_incorrect_ok (P B) :
  [* P *] (IncLoLang.stmt.assumes B)[* IncLoLang.LogicType.ok: (λ σ, P σ ∧ B σ) *] :=
begin
  rintros state ⟨ hState, hB⟩ ,
  use state,
  split,
  {exact hState, },
  {exact IncLoLang.lang_semantics.assumes_ok hB, },
end

/-! ## Variables and Mutation -/

/- Assignment -/
lemma assignment_correct (P: IncLoLang.prop) (x e) :
  [* P *]([x ↣ e])[* IncLoLang.LogicType.ok: λ σ', (∃ x': ℤ, (P{x ↣ x'} σ') ∧ σ' x = (e (σ'{x ↦ x'}))) *] :=
begin
  /- Given there exists a x' st P{x ↦ x'} σ' and σ' = e (σ'{x ↦ x'}) -/
  /- x' is the value of x *before* assignment -/
  rintros σ' hσ',

  /- recover the x' -/
  rcases hσ' with ⟨x', ⟨ hPσ', hES⟩ ⟩ ,

  /- hES says that the value of x' after assignment is the value of e with state σ'{x ↦ x'} -/
  unfold IncLoLang.prop.update_val at hPσ',

  /- Recover the start state -/
  use σ'{x ↦ x'},

  split,
  {
    exact hPσ',
  },
  {
    -- s = σ'{x ↦ x'}
    -- s{x ↦ (e s)}

    have H2: σ' = (σ'{x ↦ x'}){x ↦ e (σ'{x ↦ x'})}, {
      apply funext,
      intro v,
      by_cases v = x,
      {finish,},
      {finish,}
    },

    nth_rewrite 1 H2,
    exact IncLoLang.lang_semantics.assign,
  },
end

lemma non_det_assignment_incorrect (P: IncLoLang.prop) (x) :
  [* P *](IncLoLang.stmt.non_det_assign x)[* IncLoLang.LogicType.ok: λ σ, ∃ x': ℤ, (P{x ↣ x'}) σ *] :=
begin
  /- Given there exists a x' st P{x ↦ x'} σ' and σ' = e (σ'{x ↦ x'}) -/
  /- x' is the value of x *before* assignment -/
  rintros σ' hσ',

  /- recover the x' -/
  rcases hσ' with ⟨x', hPσ'⟩ ,

  -- /- Recover the start state -/
  -- rcases hPσ' with ⟨ σ, ⟨ hPσ, hσσ' ⟩ ⟩,
  -- use σ,
  use σ'{x ↦ x'},

  unfold IncLoLang.prop.update_val at hPσ',

  split,
  {
    exact hPσ',
  },
  {
    have H: σ' = σ'{x ↦ x'}{x ↦ σ' x}, {
      apply funext,
      intro v,
      by_cases x = v,
      {finish,},
      {finish,}
    },
    nth_rewrite 1 H,

    exact IncLoLang.lang_semantics.non_det_assign (σ' x)
  },
end

/- Costancy -/
/- Consistency for the seq case -/
lemma helper_consistency_seq (F: IncLoLang.prop) (leftC rightC: IncLoLang.stmt) (σstart σend: IncLoLang.state)
  (H1: (leftC;;rightC).Mod ∩ (F.Free) = ∅)
  (hLeft: (leftC.Mod ∩ F.Free = ∅) → 
    ∀ (ty : IncLoLang.LogicType) (σ σ' : IncLoLang.state), IncLoLang.lang_semantics leftC ty σ σ' → (F σ ↔ F σ'))
  (hRight: (rightC.Mod ∩ F.Free = ∅) → 
    ∀ (ty : IncLoLang.LogicType) (σ σ' : IncLoLang.state), IncLoLang.lang_semantics rightC ty σ σ' → (F σ ↔ F σ')):
  ∀ ty, IncLoLang.lang_semantics (leftC ;; rightC) ty σstart σend → (F σstart ↔ F σend) :=
begin
    intro ty,
    intro hσ,
    have freeLeft: (leftC.Mod ∩ F.Free = ∅), {
      have hMod := IncLoLang.mod_elem_left_elem_seq leftC rightC,
      have H:=(IncLoLang.prop.Free F).inter_subset_inter_left hMod,
      rw H1 at H,
      exact set.subset_eq_empty H rfl,
    },
    have freeRight: (rightC.Mod ∩ F.Free = ∅), {
      have hMod := IncLoLang.mod_elem_right_elem_seq leftC rightC,
      have H:=(IncLoLang.prop.Free F).inter_subset_inter_left hMod,
      rw H1 at H,
      exact set.subset_eq_empty H rfl,
    },
    cases hσ,
    {
      -- Seq okay case
      rename hσ_t σmid,
      split,
      {
        intro hσstart,
        have hMID: F σmid, {
          exact (hLeft freeLeft IncLoLang.LogicType.ok σstart σmid hσ_H1).1 hσstart,
        },
        exact (hRight freeRight ty σmid σend hσ_H2).1 hMID,
      },
      {
        intro hσend,
        have hMID: F σmid, {
          exact (hRight freeRight ty σmid σend hσ_H2).2 hσend,
        },
        exact (hLeft freeLeft IncLoLang.LogicType.ok σstart σmid hσ_H1).2 hMID,
      },
    },
    {
      -- Seq error case 2
      split,
      {
        intro hσstart,
        exact (hLeft freeLeft IncLoLang.LogicType.er σstart σend hσ_H1).1 hσstart,
      },
      {
        intro hσend,
        exact (hLeft freeLeft IncLoLang.LogicType.er σstart σend hσ_H1).2 hσend,
      },
    },
end

/- Consistency for the star case -/
lemma star_helper {F: IncLoLang.state → Prop} {C: IncLoLang.stmt} :
  (∀ ty σ σ', IncLoLang.lang_semantics C ty σ σ' → (F σ ↔ F σ')) → 
    (∀ ty σ σ', IncLoLang.lang_semantics (C**) ty σ σ' → (F σ ↔ F σ')) :=
begin
  intros h ty σ σ',
  intro Hls,
  -- intro h',
  cases Hls,

  have H: ∀ i ty σ σ', IncLoLang.lang_semantics (IncLoLang.repeat C i) ty σ σ' → (F σ ↔ F σ'),
  {
    intro i,
    induction i,
    {
      intros σ σ' ty h,
      split,
      repeat {
        intro hσ,
        rw IncLoLang.repeat at h,
        cases h,
        exact hσ,
      },
    },
    {
      rw IncLoLang.repeat,
      intros ty startState endState,
      intros h',
      split,
      { 
        intro hStart,
        cases h',
        {
          have hmid := (i_ih IncLoLang.LogicType.ok startState h'_t h'_H1).1 hStart,
          exact (h ty h'_t endState h'_H2).1 hmid,
        },
        {
          exact (i_ih IncLoLang.LogicType.er startState endState h'_H1).1 hStart,
        },
      },
      { 
        intro hEnd,
        cases h',
        {
          have hmid := (h ty h'_t endState h'_H2).2 hEnd,
          exact (i_ih IncLoLang.LogicType.ok startState h'_t h'_H1).2 hmid,
        },
        {
          exact (i_ih IncLoLang.LogicType.er startState endState h'_H1).2 hEnd,
        },
      },
    },
  },

  exact H Hls_i ty σ σ' Hls_h,
end

lemma set_func {x: Type} {A B C: set x} :
  (A ∩ (B \ C)) = (A \ C) ∩ B :=
begin
  ext,
  finish,
end

-- Want to show, if Mod(C) \ Free(F) = ∅ then constancy
lemma consistency_helper {C: IncLoLang.stmt} 
  (F: IncLoLang.prop) 
  (H1: C.Mod ∩ F.Free = ∅):
  ∀ ty σ σ', IncLoLang.lang_semantics C ty σ σ' → (F σ ↔ F σ') :=
begin
  induction C generalizing F,
  case IncLoLang.stmt.skip {
    intros ty σ σ' H2,
    cases H2,
    exact iff.rfl,
  },
  case IncLoLang.stmt.assign {
    intros ty σ σ' H2,

    unfold IncLoLang.stmt.Mod at H1,
    simp at H1,

    unfold has_mem.mem at H1,
    have H1 := IncLoLang.not_free_prop H1,
    cases H2,
    exact H1 σ (C_ᾰ_1 σ),
  },
  case IncLoLang.stmt.non_det_assign {
    intros ty σ σ' H2,
    unfold IncLoLang.stmt.Mod at H1,
    simp at H1,
    unfold has_mem.mem at H1,
    have H1 := IncLoLang.not_free_prop H1,
    cases H2,
    specialize H1 σ H2_v,
    exact H1,
  },
  case IncLoLang.stmt.seq {
    rename C_ᾰ leftC,
    rename C_ᾰ_1 rightC,
    rename C_ih_ᾰ hLeft,
    rename C_ih_ᾰ_1 hRight,

    intros ty σ σ',
    exact helper_consistency_seq F leftC rightC σ σ' H1 (hLeft F) (hRight F) ty,
  },
  case IncLoLang.stmt.error {
    intros ty σ σ' h,
    cases h,
    exact iff.rfl,
  },
  case IncLoLang.stmt.assumes {
    intros σ σ' ty h,
    cases h,
    exact iff.rfl,
  },
  case IncLoLang.stmt.choice {
    rename C_ᾰ leftC,
    rename C_ᾰ_1 rightC,
    rename C_ih_ᾰ hLeft,
    rename C_ih_ᾰ_1 hRight,
    intros σ σ' ty h,
    have freeLeft: (leftC.Mod ∩ IncLoLang.prop.Free F = ∅), {
      have hMod := IncLoLang.mod_elem_left_elem_choice leftC rightC,
      have H:=(IncLoLang.prop.Free F).inter_subset_inter_left hMod,
      rw H1 at H,
      exact set.subset_eq_empty H rfl,
    },
    have freeRight: (rightC.Mod ∩ IncLoLang.prop.Free F = ∅), {
      have hMod := IncLoLang.mod_elem_right_elem_choice leftC rightC,
      have H:=(IncLoLang.prop.Free F).inter_subset_inter_left hMod,
      rw H1 at H,
      exact set.subset_eq_empty H rfl,
    },

    cases h,
    { exact hLeft F freeLeft σ σ' ty h_h, },
    { exact hRight F freeRight σ σ' ty h_h, },
  },
  case IncLoLang.stmt.star {
    -- Star case
    rename C_ᾰ C,
    intro ty,
    intros startst endst,
    intro h,

    rw IncLoLang.stmt.Mod at H1,
    specialize C_ih F H1,

    exact (star_helper C_ih) ty startst endst h,
  },
end

lemma constancy {P Q F: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType}
  (H1: C.Mod ∩ F.Free = ∅) (H2: [* P *]C[* ty: Q *] ):
  [* λ σ, P σ ∧ F σ *]C[* ty: λ σ, Q σ ∧ F σ *] :=
begin
  rintros σ' ⟨ hσQ, hσF⟩,
  specialize H2 σ' hσQ,
  rcases H2 with ⟨ σ, ⟨ hσ', hσ''⟩ ⟩ ,
  use σ,
  split,
  {
    simp,
    split,
    { exact hσ', },
    {
      exact (consistency_helper F H1 ty σ σ' hσ'').2 hσF,
    },
  },
  {exact hσ'',},
end

lemma star_seq {P Q: IncLoLang.state → Prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType}:
  ([* P *]C** ;; C[* ty: Q *]) → ([* P *]C**[* ty: Q *]) :=
begin
  intros h σend hQσend,
  specialize h σend hQσend,
  rcases h with ⟨ σstart, ⟨ hσstart, hlang ⟩ ⟩ ,
  use σstart,
  split,
  { exact hσstart, },
  { exact IncLoLang.start_seq hlang, },
end

/- Backwards variant -/
lemma backwards_variant {P: ℕ → IncLoLang.state → Prop} {C: IncLoLang.stmt}
  (H1: ∀ n, [* P n *]C[* IncLoLang.LogicType.ok: P n.succ *] ):
  [* P 0 *]C**[* IncLoLang.LogicType.ok: λ σ, ∃ N, P N σ *] :=
begin
  intros σ hσ,
  cases hσ with n hσ,
  revert σ, 
  induction n,
  {
    intros σ hσ,
    use σ,
    split,
    { exact hσ, },
    {
      apply IncLoLang.lang_semantics.star 0,
      exact IncLoLang.lang_semantics.skip,
    }
  },
  { exact iterate_non_zero_incorrect (seq_normal_incorrect _ n_ih (H1 n_n)), }
end

-- lemma local_variable {P C Q ty} {y x: string} 
--   (H₁: [* P *] C{y//x} [* ty: Q *]) 
--   (H₂: y ∉ (IncLoLang.prop.Free P ∪ IncLoLang.stmt.Free C))
--   (H₃: y ≠ x): 
--     [* P *] [loc x . C ] [* ty: λ σ, ∃ v_y: ℤ, Q (σ{y ↦ v_y}) *] :=
-- begin
--   -- Following proof in the paper
--   -- Suppose [p]C(y/x)[ε:q] and (σq | x → v,y → vy) ∈ ∃y.q.
--   intros σq Hσq,
--   -- (vy = σq y)
--   -- (v = σq x)
--   -- Then (σq |x→v,y→v2) ∈ q for some v2
--   cases Hσq with v₂,

--   -- We execute C(y/x) backwards and get (σp | x → v, y → v1) ∈ p by the Characterization Lemma.
--   specialize H₁ (σq{y ↦ v₂}) Hσq_h,
--   rcases H₁ with ⟨ σp, ⟨ hσp, hls ⟩ ⟩,
--   -- v1 = σp y 
--   have Hxpq : σp x = σq x, { sorry, }, -- Prove x is the same as y doesnt touch x

--   -- Since p is independent of y we can set y back to vy and it will still be in p: (σp | x → v,y → vy) ∈ p.
--   have hσq' : P (σp{y ↦ σq y}), {
--     have hyFree: y ∉ IncLoLang.prop.Free P, {by_contra, apply H₂, left, exact h,}, 
--     have hyFree := IncLoLang.not_free_prop hyFree,
--     exact (hyFree σp (σq y)).mp hσp,
--   },

--   have hyFreeC: y ∉ IncLoLang.stmt.Free C, {by_contra, apply H₂, right, exact h,}, 
--   have hyFreeC := IncLoLang.free_language_semantics C y hyFreeC, 
--   -- This sequence of steps can be mimicked in the semantics of local x.C, 
--   -- stepping from (σq | x → v,y → vy) via backwards finalization to (σq |x → v,y → vy),
--   use (σp{y ↦ σq y}),
--   -- then backwards via C to (σp |x → v, y → vy), and then via backwards initialization to (σp |x → v,y → vy)
--   split,
--   {
--     exact hσq',
--   },
--   {
--     -- have H: σp{y ↦ σq y} = σp{y ↦ σq y}{x ↦ 0}, {sorry,},
--     -- rw H,
--     -- have H: σq = σq{x ↦ 0}, {sorry,},
--     -- rw H,
--     rw ← IncLoLang.update_id x σp,
--     rw IncLoLang.update_swap _ _ _ _ _ H₃,
--     nth_rewrite 1 ← IncLoLang.update_id x σq,
--     rw Hxpq,

--     apply IncLoLang.lang_semantics.local_var x (σq x),

--     have H₄ : y ∉ C.Free, { by_contra, apply H₂, right, exact h, },
--     have H₅ : x ∉ C{y // x}.Free, {sorry,},
--     have H₅ := IncLoLang.substitution_rule (ne.symm H₃) H₅ hls, 

--     have H: C{y//x}{x//y} = C, {sorry,}, -- Use y ∉ C.Free

--     rw H at H₅,

--   }
-- end

lemma substitution_1 {P Q ty} {C: IncLoLang.stmt} {e: IncLoLang.expression} {x: string} 
  (HB: (∃ B: set string, (e.FreeProp B ∧ B.finite)))
  (H₁: [* P *]C[* ty: Q *]) (H₂: (e.Free ∪ {x}) ∩ C.Free = ∅): 
  [* λ σ, P (σ{x ↦ e σ}) *] C [* ty: λ σ, Q (σ{x ↦ e σ}) *] := 
begin
  intros σ' hσ',
  specialize H₁ (σ'{x ↦ e σ'}) hσ',
  rcases H₁ with ⟨ σ, ⟨ hpσ, hls⟩ ⟩ ,
  use σ{x ↦ σ' x}, 
  have HxFree : x ∉ C.Free, {  
    by_contra, 
    apply set.eq_empty_iff_forall_not_mem.mp H₂ x,
    split,
    right,
    exact set.mem_singleton x,
    exact h
  },
  split,
  {
    simp,
    have H: e (σ{x ↦ σ' x}) = σ x, {
      rw IncLoLang.stmt_free_unchanged (⟨ hls, HxFree⟩ ),
      rw IncLoLang.state.update_apply,
      apply IncLoLang.for_all_free_expression,
      intros y hy,
      by_cases hxy: x = y,
      {
        cases hxy,
        rw IncLoLang.state.update_apply,
      },
      {
        have Hy: y ∉ C.Free, {
          by_contra,
          apply set.eq_empty_iff_forall_not_mem.mp H₂ y,
          split,
          left,
          exact hy,
          exact h,
        },
        rw IncLoLang.state.update_apply_ne _ _ _ _ (ne.symm hxy),
        have H: IncLoLang.lang_semantics C ty σ (σ'{x ↦ e σ'}) ∧ x ∉ C.Free, { exact ⟨hls, HxFree⟩ },

        rw IncLoLang.stmt_free_unchanged (⟨hls, Hy⟩),
        rw IncLoLang.state.update_apply_ne _ _ _ _ (ne.symm hxy),
      },
      exact HB,
    },
    rw H,
    rw IncLoLang.state.update_id,
    exact hpσ,
  },
  {
    have H := IncLoLang.free_language_semantics _ _ HxFree _ _ _ (σ' x) hls,
    rw IncLoLang.state.update_override at H,
    rw IncLoLang.state.update_id at H,
    exact H,
  },
end

lemma substitution_2 {P Q: IncLoLang.prop} {C ty} {x y: string} 
  (H₁: [* P *]C[* ty: Q *]) (H₂: y ∉ C.Free ∪ P.Free ∪ Q.Free) (H₃: x ≠ y): 
  [* P[y//x] *] C{y // x} [* ty: Q[y//x] *] := 
begin
  intros σ' hσ',
  unfold IncLoLang.prop.substitute at hσ',
  specialize H₁ (σ'⟨x//y⟩) hσ', 

  rcases H₁ with ⟨ σ, ⟨ hpσ, hC ⟩⟩,

  use σ⟨ y // x ⟩{x ↦ σ' x}, 

  split,
  {
    unfold IncLoLang.prop.substitute,
    unfold IncLoLang.state.substitute,
    simp,
    rw IncLoLang.state.update_swap _ _ _ _ _ H₃,
    -- rw IncLoLang.state.update_swap _ _ _ _ _ H₃,
    simp,
    have H: y ∉ P.Free, {
      by_contra,
      apply H₂,
      left, right,
      exact h,
    },
    simp[(ne.symm H₃)],
    exact (IncLoLang.not_free_prop H σ (0)).1 hpσ,
  },
  {
    have H: y ∉ C.Free, {
      by_contra,
      apply H₂,
      left, left,
      exact h,
    },

    have H := IncLoLang.substitution_rule (ne.symm H₃) H hC,

    have Ht: σ'⟨x//y⟩⟨y//x⟩ = σ'{x ↦ 0}, { 
      funext z,
      by_cases hzx: z = x,
      {
        cases hzx,
        unfold IncLoLang.state.substitute,
        simp[H₃],
      },
      {
        by_cases hyz: z = y,
        {
          cases hyz,
          unfold IncLoLang.state.substitute,
          simp[hzx],
        },
        {
          unfold IncLoLang.state.substitute,
          simp[hzx, hyz],
        },
      }
    },
    rw Ht at H,

    have HxFree: x ∉ (C{y//x}).Free, {exact IncLoLang.stmt.substitution.x_free H₃,},
    have HLS := IncLoLang.free_language_semantics (C{y // x}) x HxFree (σ⟨y//x⟩) (σ'{x ↦ 0}) ty (σ' x) H,
    simp at HLS,
    exact HLS,
  },
end

end IncLogic
