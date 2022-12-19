
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

/- Q: What to do about locals? -/
/- Q: Check def of demantics of C**? -/

/- the def of post from the paper-/
def post (ty: IncLoLang.LogicType) (r: IncLoLang.stmt) (p: IncLoLang.state -> Prop) : IncLoLang.state -> Prop 
  := λ σ', ∃ σ, p σ ∧ IncLoLang.lang_semantics r ty σ σ'


/-! ## Incorrectness logic and Hoare logic encodings -/
def incorrectness_stmt (type: IncLoLang.LogicType) (P : (IncLoLang.state) → Prop) (R : IncLoLang.stmt)
  (Q : (IncLoLang.state) → Prop) : Prop := 
  ∀ state, Q state -> ((post type R) P) state

def hoare_stmt (type: IncLoLang.LogicType) (P : (IncLoLang.state) → Prop) (R : IncLoLang.stmt)
  (Q : (IncLoLang.state) → Prop) : Prop := 
  ∀ state, ((post type R) P) state -> Q state

/-! ## Notation -/
notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` ty: 2 :=
  hoare_stmt ty P S Q

notation `[* ` P : 1 ` *] ` S : 1 ` [* ` Q : 1 ` *]` ty: 2 :=
  incorrectness_stmt ty P S Q

/-! ## Lemmas-/
lemma hoare_skip_intro_ok { P: IncLoLang.state -> Prop } : {* P *} IncLoLang.stmt.skip {* P *} IncLoLang.LogicType.ok:=
begin
  intros state h,

  rcases h with ⟨σ, ⟨h₁, h₂⟩⟩,

  cases h₂,
  finish,
end

lemma inc_skip_intro_er { P: IncLoLang.state -> Prop } : [* P *] IncLoLang.stmt.error [* P *] IncLoLang.LogicType.er :=
begin
  intros state h,

  use state,

  split,
  { finish, },
  { exact IncLoLang.lang_semantics.error },
end

lemma seq_intro_hoare {P Q R S T} (hS : {* P *} S {* Q *} IncLoLang.LogicType.ok)
    (hT : {* Q *} T {* R *} IncLoLang.LogicType.ok) :
  {* P *} S ;; T {* R *} IncLoLang.LogicType.ok :=
begin
  intros end_state,
  intro hST,
  specialize hT end_state,
  apply hT,
  rcases hST with ⟨start_state, ⟨start_P, hST⟩ ⟩,
  cases hST,
  use hST_t,
  split,  
  {
    specialize hS hST_t,
    apply hS,
    use start_state,
    split,
    { exact start_P, },
    { exact hST_H1, },
  },
  {
    exact hST_H2,
  },
end

/-! ## Incorrectness rules -/

/- Empty under approximates -/ 
lemma empty_under_incorrect {P C ty} : [* P *] C [* λ st, false *] ty :=
begin
  intro state,
  finish,
end

/- Consequence-/
lemma consequence_incorrect {P Q C ty} 
  {P': IncLoLang.state -> Prop} 
  {Q': IncLoLang.state -> Prop} (h : [* P *] C [* Q *]ty) (hQ: ∀ st, Q' st -> Q st) (hP: ∀ st, P st -> P' st):
  [* P' *] C [* Q' *]ty :=
begin
  intros state hQ',
  specialize hQ state hQ',
  specialize h state hQ,
  rcases h with ⟨ start_state, ⟨ hP₂, lang ⟩ ⟩ ,
  use start_state,
  exact ⟨hP start_state hP₂, lang⟩,
end

/- Disjunction -/
lemma disjunction_incorrect {P₁ P₂ Q₁ Q₂ C ty} 
  (h₁ : [* P₁ *] C [* Q₁ *] ty) 
  (h₂ : [* P₂ *] C [* Q₂ *] ty):
  [* λ st, P₁ st ∨ P₂ st *] C [* λ st, Q₁ st ∨ Q₂ st *] ty :=
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
lemma unit_incorrect_ok {P} : [* P *] IncLoLang.stmt.skip [* P *] IncLoLang.LogicType.ok :=
begin
  intros end_state hP,
  use end_state,
  split,
  { exact hP,},
  { exact IncLoLang.lang_semantics.skip, },
end

/- Unit Err -/
lemma unit_incorrect_err {P} : [* P *] IncLoLang.stmt.skip [* λ _, false *] IncLoLang.LogicType.er :=
begin
  intros end_state hP,
  use end_state,
end

/- Sequencing short circuit -/ 
lemma seq_short_circuit_incorrect {P R S} {T: IncLoLang.stmt} (hS : [* P *] S [* R *] IncLoLang.LogicType.er) :
  [* P *] S ;; T [* R *] IncLoLang.LogicType.er :=
begin
  intros end_state hStartR,
  specialize hS end_state hStartR,
  rcases hS with ⟨ start_state, ⟨ hP, hS ⟩  ⟩ ,
  use start_state,
  exact ⟨ hP, IncLoLang.lang_semantics.seq_er_1 hS⟩,
end

/- Sequencing normal -/ 
lemma seq_normal_incorrect {P Q R S T ty} (hS : [* P *] S [* Q *] IncLoLang.LogicType.ok)
    (hT : [* Q *] T [* R *] ty) :
  [* P *] S ;; T [* R *] ty :=
begin
  intros end_state hStartR,
  specialize hT end_state hStartR,
  rcases hT with ⟨ mid_state, ⟨ hMidQ, r⟩ ⟩,
  specialize hS mid_state hMidQ,
  rcases hS with ⟨ start_state, ⟨ hStartP, t⟩ ⟩,
  use start_state,
  split,
  { exact hStartP, },
  {
    cases ty,
    { exact IncLoLang.lang_semantics.seq_er_2 t r },
    { exact IncLoLang.lang_semantics.seq_ok t r },
  },
end

/- Iterate zero -/
lemma iterate_zero_incorrect {C P} :
  [* P *] (C**) [* P *]IncLoLang.LogicType.ok :=
begin
  intros state hState,
  use state,
  split,
  { exact hState, },
  { exact IncLoLang.lang_semantics.star_base, },
end

/- Iterate non-zero -/
lemma iterate_non_zero_incorrect {C P Q ty} (h: [* P *] C** ;; C [* Q *]ty):
  [* P *] (C**) [* Q *]ty :=
begin
  intros state hState,
  specialize h state hState,
  rcases h with ⟨ bState, ⟨ hBState, h ⟩ ⟩ ,
  use bState,
  split,
  { exact hBState, },
  { exact IncLoLang.lang_semantics.star_recurse h, }
end

/- Choice left -/
lemma choice_left_incorrect {C₁ C₂ P Q ty} (h: [* P *] C₁ [* Q *]ty):
  [* P *] (C₁.choice C₂)  [* Q *]ty :=
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
lemma choice_right_incorrect {C₁ C₂ P Q ty} (h: [* P *] C₂ [* Q *]ty):
  [* P *] (IncLoLang.stmt.choice C₁ C₂)  [* Q *]ty :=
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
  [* P *] (IncLoLang.stmt.error)  [* P *]IncLoLang.LogicType.er :=
begin
  intros state hState,
  use state,
  split,
  { exact hState, },
  { exact IncLoLang.lang_semantics.error, },
end

/- Error ok -/
lemma error_ok_incorrect {P}:
  [* P *] (IncLoLang.stmt.error)  [* λ st, false *]IncLoLang.LogicType.ok :=
begin
  intros state hState,
  use state,
end

/- Assume ok -/
lemma assume_incorrect_ok {P B} :
  [* P *] (IncLoLang.stmt.assumes B)[* (λ st, P st ∧ B st) *]IncLoLang.LogicType.ok :=
begin
  rintros state ⟨ hState, hB⟩ ,
  use state,
  split,
  {exact hState, },
  {exact IncLoLang.lang_semantics.assumes_ok hB, },
end

/- Assume er -/
lemma assume_incorrect_er {P B} :
  [* P *] (IncLoLang.stmt.assumes B)[* λ st, false *]IncLoLang.LogicType.er :=
begin
  intros state hState,
  use state,
  /- The fact this is so easy is a little concerning -/
end

/-! ## Variables and Mutation -/


/- Assignment -/
lemma assignment_correct {P x e} :
  [* P *](IncLoLang.stmt.assign x e)[* λ σ', (∃ x', (P{x ↦ x'} σ') ∧ σ' x = (e (σ'{x ↦ x'}))) *] IncLoLang.LogicType.ok :=
begin
  /- Given there exists a x' st P{x ↦ x'} σ' and σ' = e (σ'{x ↦ x'}) -/
  /- x' is the value of x *before* assignment -/
  rintros σ' hσ',

  /- recover the x' -/
  rcases hσ' with ⟨x', ⟨ hPσ', hES⟩ ⟩ ,
  simp at hES,

  /- hES says that the value of x' after assignment is the value of e with state σ'{x ↦ x'} -/

  /- Recover the start state -/
  rcases hPσ' with ⟨ σ, ⟨ hPσ, hσσ' ⟩ ⟩,

  use σ,

  split,
  {
    exact hPσ,
  },
  {
    have H2: σ' = σ{x ↦ e σ}, {
      apply funext,
      intro v,
      by_cases v = x,
      {finish,},
      {finish,}
    },
    rw H2,

    exact IncLoLang.lang_semantics.assign
  },
end

/- Assignment er -/
lemma assignment_incorrect_er {P x e} :
  [* P *](IncLoLang.stmt.assign x e)[* λ_, false *] IncLoLang.LogicType.er :=
begin
  finish,
end

lemma non_det_assignment_incorrect {P x} :
  [* P *](IncLoLang.stmt.non_det_assign x)[* λ σ, ∃ x', P{x ↦ x'} σ *] IncLoLang.LogicType.ok :=
begin
  /- Given there exists a x' st P{x ↦ x'} σ' and σ' = e (σ'{x ↦ x'}) -/
  /- x' is the value of x *before* assignment -/
  rintros σ' hσ',

  /- recover the x' -/
  rcases hσ' with ⟨x', hPσ'⟩ ,

  /- Recover the start state -/
  rcases hPσ' with ⟨ σ, ⟨ hPσ, hσσ' ⟩ ⟩,

  use σ,

  split,
  {
    exact hPσ,
  },
  {
    have H: σ' = σ{x ↦ σ' x}, {
      apply funext,
      intro v,
      by_cases x = v,
      {finish,},
      {finish,}
    },
    rw H,
    exact IncLoLang.lang_semantics.non_det_assign
  },
end

-- lemma constancy {P Q F: IncLoLang.state -> Prop} {C: IncLoLang.stmt} 
--   (H1: ∀ x, ¬IncLoLang.Mod(C)(x) || ¬IncLoLang.Free(F)(x)) (H2: [* P *]C[* Q *]):
--   [* λ st, P st ∧ F st *]C[* λ st, Q st ∧ F st *] :=
-- begin
--   sorry
-- end

/-! ### TODO: 

- [x] Assignment
- [x] Nondet Assignment
- [ ] Constancy
- [ ] Local variable !!
- [ ] Substitution 1
- [ ] Substitution 2
- [ ] Backwards varient

-/