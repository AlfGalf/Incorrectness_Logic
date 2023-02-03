
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
  { 
    have h : IncLoLang.lang_semantics (IncLoLang.repeat C 0) IncLoLang.LogicType.ok state state, {
      rw IncLoLang.repeat,
      exact IncLoLang.lang_semantics.skip,
    },
    exact IncLoLang.lang_semantics.star 0 h, 
  },
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
  { 
    cases h, 
    {
      cases h_H1,
      have H: IncLoLang.lang_semantics (IncLoLang.repeat C (nat.succ h_H1_i)) IncLoLang.LogicType.ok bState state, {
        rw IncLoLang.repeat,
        exact IncLoLang.lang_semantics.seq_ok (h_H1_h) (h_H2)
      },
      exact IncLoLang.lang_semantics.star (nat.succ h_H1_i) H,
    },
    {
      cases h_H1,
      have H: IncLoLang.lang_semantics (IncLoLang.repeat C (nat.succ h_H1_i)) IncLoLang.LogicType.er bState state, {
        rw IncLoLang.repeat,
        exact IncLoLang.lang_semantics.seq_er_2 (h_H1_h) (h_H2)
      },
      exact IncLoLang.lang_semantics.star (nat.succ h_H1_i) H,
    },
    { exact h_H1, },
  }
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
  [* P *](IncLoLang.stmt.assign x e)[* λ σ', (∃ x', (P{x ↣ x'} σ') ∧ σ' x = (e (σ'{x ↦ x'}))) *] IncLoLang.LogicType.ok :=
begin
  /- Given there exists a x' st P{x ↦ x'} σ' and σ' = e (σ'{x ↦ x'}) -/
  /- x' is the value of x *before* assignment -/
  rintros σ' hσ',

  /- recover the x' -/
  rcases hσ' with ⟨x', ⟨ hPσ', hES⟩ ⟩ ,

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
  [* P *](IncLoLang.stmt.non_det_assign x)[* λ σ, ∃ x', P{x ↣ x'} σ *] IncLoLang.LogicType.ok :=
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

lemma helper_seq (F: IncLoLang.state -> Prop) (leftC rightC: IncLoLang.stmt) (σstart σend: IncLoLang.state)
  (H1: ∀ x, x ∈ IncLoLang.Mod (leftC;;rightC) → (IncLoLang.Free(F)(x)))
  (hLeft: (∀ (x : string), x ∈ IncLoLang.Mod leftC → IncLoLang.Free F x) → ∀ (ty : IncLoLang.LogicType) (σ σ' : IncLoLang.state), IncLoLang.lang_semantics leftC ty σ σ' → (F σ ↔ F σ'))
  (hRight: (∀ (x : string), x ∈ IncLoLang.Mod rightC → IncLoLang.Free F x) → ∀ (ty : IncLoLang.LogicType) (σ σ' : IncLoLang.state), IncLoLang.lang_semantics rightC ty σ σ' → (F σ ↔ F σ')):
  ∀ ty, IncLoLang.lang_semantics (leftC ;; rightC) ty σstart σend → (F σstart ↔ F σend) :=
begin
    intro ty,
    intro hσ,
    have freeLeft: (∀ (x : string), x ∈ IncLoLang.Mod leftC → IncLoLang.Free F x), {
      intro x,
      intro hx,
      have hMod := IncLoLang.mod_elem_left_elem_seq leftC rightC x hx,
      specialize H1 x hMod,
      exact H1,
    },
    have freeRight: (∀ (x : string), x ∈ IncLoLang.Mod rightC → IncLoLang.Free F x), {
      intro x,
      intro hx,
      have hMod := IncLoLang.mod_elem_right_elem_seq leftC rightC x hx,
      specialize H1 x hMod,
      exact H1,
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
        exact (hRight freeRight IncLoLang.LogicType.ok σmid σend hσ_H2).1 hMID,
      },
      {
        intro hσend,
        have hMID: F σmid, {
          exact (hRight freeRight IncLoLang.LogicType.ok σmid σend hσ_H2).2 hσend,
        },
        exact (hLeft freeLeft IncLoLang.LogicType.ok σstart σmid hσ_H1).2 hMID,
      },
    },
    {
      -- Seq error case 2
      rename hσ_t σmid,
      split,
      {
        intro hσstart,
        have hMID: F σmid, {
          exact (hLeft freeLeft IncLoLang.LogicType.ok σstart σmid hσ_H1).1 hσstart,
        },
        exact (hRight freeRight IncLoLang.LogicType.er σmid σend hσ_H2).1 hMID,
      },
      {
        intro hσend,
        have hMID: F σmid, {
          exact (hRight freeRight IncLoLang.LogicType.er σmid σend hσ_H2).2 hσend,
        },
        exact (hLeft freeLeft IncLoLang.LogicType.ok σstart σmid hσ_H1).2 hMID,
      }
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

-- | star_base {C s ty} :
--   lang_semantics (IncLoLang.stmt.star C) ty s s
-- | star_recurse {C s₁ s₂ ty} (h: lang_semantics (C** ;; C) ty s₁ s₂):
--   lang_semantics (C**) ty s₁ s₂

lemma star_helper {F: IncLoLang.state -> Prop} {C: IncLoLang.stmt} :
  (∀ ty σ σ', IncLoLang.lang_semantics C ty σ σ' → (F σ ↔ F σ')) → (∀ ty σ σ', IncLoLang.lang_semantics (C**) ty σ σ' → (F σ ↔ F σ')) :=
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
          exact (h IncLoLang.LogicType.ok h'_t endState h'_H2).1 hmid,
        },
        {
          have hmid := (i_ih IncLoLang.LogicType.ok startState h'_t h'_H1).1 hStart,
          exact (h IncLoLang.LogicType.er h'_t endState h'_H2).1 hmid,
        },
        {
          exact (i_ih IncLoLang.LogicType.er startState endState h'_H1).1 hStart,
        },
      },
      { 
        intro hEnd,
        cases h',
        {
          have hmid := (h IncLoLang.LogicType.ok h'_t endState h'_H2).2 hEnd,
          exact (i_ih IncLoLang.LogicType.ok startState h'_t h'_H1).2 hmid,
        },
        {
          have hmid := (h IncLoLang.LogicType.er h'_t endState h'_H2).2 hEnd,
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

-- Want to show, if Mod(C) \ Free(F) = ∅ then constancy
lemma helper {F: IncLoLang.state -> Prop} {C: IncLoLang.stmt} 
  (H1: ∀ x, x ∈ IncLoLang.Mod(C) → (IncLoLang.Free(F)(x))):
  ∀ ty σ σ', IncLoLang.lang_semantics C ty σ σ' → (F σ ↔ F σ') :=
begin
  induction C,
  case IncLoLang.stmt.skip {
    intros ty σ σ' H2,
    cases H2,
    exact iff.rfl,
  },
  case IncLoLang.stmt.assign {
    intros ty σ σ' H2,
    --  hσ,
    specialize H1 C_ᾰ,
    unfold IncLoLang.Mod at H1,
    simp at H1,
    unfold IncLoLang.Free at H1,
    specialize H1 σ (C_ᾰ_1 σ),

    cases H2,
    exact H1,
  },
  case IncLoLang.stmt.non_det_assign {
    intros ty σ σ' H2,
    specialize H1 C,
    unfold IncLoLang.Mod at H1,
    simp at H1,
    unfold IncLoLang.Free at H1,
    specialize H1 σ,
    cases H2,
    specialize H1 H2_v,
    exact H1,
  },
  case IncLoLang.stmt.seq {
    rename C_ᾰ leftC,
    rename C_ᾰ_1 rightC,
    rename C_ih_ᾰ hLeft,
    rename C_ih_ᾰ_1 hRight,

    intros ty σ σ',
    exact helper_seq F leftC rightC σ σ' H1 hLeft hRight ty,
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
    have freeLeft: (∀ (x : string), x ∈ IncLoLang.Mod leftC → IncLoLang.Free F x), {
      intros x hx,
      exact H1 x (IncLoLang.mod_elem_left_elem_choice leftC rightC x hx),
    },
    have freeRight: (∀ (x : string), x ∈ IncLoLang.Mod rightC → IncLoLang.Free F x), {
      intros x hx,
      exact H1 x (IncLoLang.mod_elem_right_elem_choice leftC rightC x hx),
    },

    cases h,
    { exact hLeft freeLeft σ σ' ty h_h, },
    { exact hRight freeRight σ σ' ty h_h, },
  },
  {
    -- Star case
    rename C_ᾰ C,
    intro ty,
    intros startst endst,
    intro h,

    rw IncLoLang.Mod at H1,
    specialize C_ih H1,

    exact (star_helper C_ih) ty startst endst h,
  },
end

lemma constancy {P Q F: IncLoLang.state -> Prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType}
  (H1: ∀ x, IncLoLang.Mod(C)(x) → (IncLoLang.Free(F)(x))) (H2: [* P *]C[* Q *]ty ):
  [* λ st, P st ∧ F st *]C[* λ st, Q st ∧ F st *]ty :=
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
      exact (helper H1 ty σ σ' hσ'').2 hσF,
    },
  },
  {exact hσ'',},
end

/-! ### TODO: 

- [x] Assignment
- [x] Nondet Assignment
- [x] Constancy
- [ ] Local variable !!
- [ ] Substitution 1
- [ ] Substitution 2
- [ ] Backwards varient

-/