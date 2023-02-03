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

namespace IncLoLang

/-! ## State-/

meta def tactic.dec_trivial := `[exact dec_trivial]

def state: Type := string -> ℕ

def state.update : string -> ℕ -> state -> state
| name val σ := (λ name', if name' = name then val else σ name')

notation s `{` name ` ↦ ` val `}` := state.update name val s

@[simp] lemma state.update_apply (name : string) (val : ℕ) (s : state) :
  s{name ↦ val} name = val :=
begin
  unfold state.update,
  finish,
end

@[simp] lemma update_apply_ne (name name' : string) (val : ℕ) (s : state)
    (h : name' ≠ name) :
  s{name ↦ val} name' = s name' :=
begin
  unfold state.update,
  exact if_neg h,
end

@[simp] lemma update_override (name : string) (val₁ val₂ : ℕ) (s : state) :
  s{name ↦ val₂}{name ↦ val₁} = s{name ↦ val₁} :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp [h]
end

@[simp] lemma update_swap (name₁ name₂ : string) (val₁ val₂ : ℕ) (s : state)
    (h : name₁ ≠ name₂ . tactic.dec_trivial) :
  s{name₂ ↦ val₂}{name₁ ↦ val₁} = s{name₁ ↦ val₁}{name₂ ↦ val₂} :=
begin
  apply funext,
  intro name',
  by_cases name' = name₁;
    by_cases name' = name₂;
    simp * at *
end

@[simp] lemma update_id (name : string) (s : state) :
  s{name ↦ s name} = s :=
begin
  apply funext,
  intro name',
  by_cases name' = name;
    simp * at *
end

@[simp] lemma update_same_const (name : string) (val : ℕ) :
  (λ_, val){name ↦ val} = (λ_, val) :=
by apply funext; simp

/-! ## Language -/

inductive stmt : Type
| skip            : stmt
| assign          : string → (state → ℕ) → stmt
| non_det_assign  : string → stmt
| seq             : stmt → stmt → stmt
| error           : stmt
| assumes         : (state → Prop) → stmt
| choice          : stmt → stmt → stmt
| star            : stmt → stmt
| local_var       : string → stmt → stmt

infixr ` ;; ` : 90 := stmt.seq

infixr ` <+> ` : 90 := stmt.choice

postfix `**` : 90 := stmt.star

notation `[` x ` ↣ ` e `]` := stmt.assign x e

notation `[loc` x `.` C `]` := stmt.local_var x C

/- This is the definition of P[x'/x] used in the paper -/
def p_thing (P: IncLoLang.state -> Prop) (x': ℕ) (x: string) : IncLoLang.state -> Prop :=
  -- λ σ', ∃ σ, P σ ∧ σ' = σ{x ↦ x'}
  -- This is the definition given int he paper but it is wrong
  λ σ', P (σ'{x ↦ x'})
-- ie, True for σ if P(σ{x ↦ x'})

notation P `{` name ` ↣ ` val `}` := p_thing P val name

/-! # Language semantics -/

inductive LogicType : Type
| er
| ok

def repeat: IncLoLang.stmt → ℕ → IncLoLang.stmt 
| C nat.zero := IncLoLang.stmt.skip
| C (nat.succ i) := (repeat C (i)) ;; C

inductive lang_semantics: IncLoLang.stmt -> LogicType -> (IncLoLang.state) -> (IncLoLang.state) -> Prop
| skip {s} :
  lang_semantics IncLoLang.stmt.skip LogicType.ok s s
| seq_ty {S T s t u ty} (H1: lang_semantics S LogicType.ok s t) (H2: lang_semantics T ty t u) :
  lang_semantics(S ;; T) ty s u
| seq_er_1 {S T s t} (H1: lang_semantics S LogicType.er s t): 
  lang_semantics (S ;; T) LogicType.er s t
| error {s}:
  lang_semantics IncLoLang.stmt.error LogicType.er s s
| assign {x s e} :
  lang_semantics (IncLoLang.stmt.assign x e) LogicType.ok s (s{x ↦ (e s)})
| non_det_assign {x s v} :
  lang_semantics (IncLoLang.stmt.non_det_assign x) LogicType.ok s (s{x ↦ v})
| assumes_ok {s} {B: IncLoLang.state -> Prop} (h: B s) :
  lang_semantics (IncLoLang.stmt.assumes B) LogicType.ok s s
| choice_left {C₁ C₂ ty s₁ s₂} (h: (lang_semantics C₁ ty s₁ s₂)): 
  lang_semantics (C₁ <+> C₂) ty s₁ s₂
| choice_right {C₁ C₂ ty s₁ s₂} (h: (lang_semantics C₂ ty s₁ s₂)): 
  lang_semantics (C₁ <+> C₂) ty s₁ s₂
| star {C s₁ s₂ ty} (i: ℕ) (h: lang_semantics (repeat C i) ty s₁ s₂):
  lang_semantics (C**) ty s₁ s₂
| local_var {C s₁ s₂ ty x v} (h: lang_semantics C ty s₁ s₂):
  lang_semantics ([loc x . C]) ty (s₁{x ↦ v}) (s₂{x ↦ v})

def Free (P: state -> Prop): set string :=
  λ x, ∀ σ v, (P σ ↔ P (σ{x ↦ v}))

def Mod: stmt -> set string
| (C₁ ;; C₂) := (Mod C₁) ∪ (Mod C₂)
| (C₁ <+> C₂) := (Mod C₁) ∪ (Mod C₂)
| (C**) := (Mod C)
| ([x ↣ v]) := {x}
| (IncLoLang.stmt.skip) := {}
| (IncLoLang.stmt.non_det_assign x) := {x}
| (IncLoLang.stmt.assumes _) := {}
| (IncLoLang.stmt.error) := {}
| (IncLoLang.stmt.local_var x C) := Mod C \ {x}

lemma mod_elem_left_elem_seq (C₁ C₂: stmt) (x: string):
   x ∈ Mod C₁ → x ∈ Mod (C₁ ;; C₂):=
begin 
  intro h,
  rw Mod,
  finish,
end

lemma mod_elem_right_elem_seq (C₁ C₂: stmt) (x: string):
   x ∈ Mod C₂ → x ∈ Mod (C₁ ;; C₂):=
begin 
  intro h,
  rw Mod,
  finish,
end

lemma mod_elem_left_elem_choice (C₁ C₂: stmt) (x: string):
   x ∈ Mod C₁ → x ∈ Mod (C₁ <+> C₂):=
begin 
  intro h,
  rw Mod,
  finish,
end

lemma mod_elem_right_elem_choice (C₁ C₂: stmt) (x: string):
   x ∈ Mod C₂ → x ∈ Mod (C₁ <+> C₂):=
begin 
  intro h,
  rw Mod,
  finish,
end

lemma mod_star_eq (C: stmt):
   Mod (C**) = Mod C :=
begin 
  rw Mod,
end

lemma start_seq {C: stmt} {σ σ': state} {ty: LogicType}:
  IncLoLang.lang_semantics (C** ;; C) ty σ σ' → IncLoLang.lang_semantics (C**) ty σ σ' :=
begin
  intro h,
  cases h,
  {
    have H: ∃ N, lang_semantics (repeat C N) ty σ σ',
    {
      cases h_H1,
      use h_H1_i.succ,
      rw repeat,
      exact lang_semantics.seq_ty h_H1_h h_H2,
    },
    cases H with N,
    exact lang_semantics.star N H_h,
  },
  {
    exact h_H1,
  },
end

lemma p_thing_free {x v} {P: state -> Prop} :
  Free (P{ x ↣ v }) = (Free P) ∪ { x } :=
begin
  apply set.eq_of_subset_of_subset,
  {
    intro y,
    unfold Free,
    sorry,
  },
  {
    intros y hx,
    cases hx,
    {
      unfold Free,
      unfold Free at hx,
      intros σ v,

    },
    {

    }

  }

end

end IncLoLang