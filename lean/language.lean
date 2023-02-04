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

/-! # Propositions -/

def prop: Type := state -> Prop

/-! # Expression -/

def expression: Type := state -> ℕ

/-! ## Language -/

inductive stmt : Type
| skip            : stmt
| assign          : string → expression → stmt
| non_det_assign  : string → stmt
| seq             : stmt → stmt → stmt
| choice          : stmt → stmt → stmt
| star            : stmt → stmt
| local_var       : string → stmt → stmt
| error           : stmt
| assumes         : prop → stmt

-- Language notation

infixr ` ;; ` : 90 := stmt.seq

infixr ` <+> ` : 90 := stmt.choice

postfix `**` : 90 := stmt.star

notation `[` x ` ↣ ` e `]` := stmt.assign x e

notation `[loc` x `.` C `]` := stmt.local_var x C

/- This is the definition of P[x'/x] used in the paper -/
def p_thing (P: prop) (x': ℕ) (x: string) : IncLoLang.state -> Prop :=
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

inductive lang_semantics: IncLoLang.stmt -> LogicType -> IncLoLang.state -> IncLoLang.state -> Prop
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
| assumes_ok {s} {B: prop} (h: B s) :
  lang_semantics (IncLoLang.stmt.assumes B) LogicType.ok s s
| choice_left {C₁ C₂ ty s₁ s₂} (h: (lang_semantics C₁ ty s₁ s₂)): 
  lang_semantics (C₁ <+> C₂) ty s₁ s₂
| choice_right {C₁ C₂ ty s₁ s₂} (h: (lang_semantics C₂ ty s₁ s₂)): 
  lang_semantics (C₁ <+> C₂) ty s₁ s₂
| star {C s₁ s₂ ty} (i: ℕ) (h: lang_semantics (repeat C i) ty s₁ s₂):
  lang_semantics (C**) ty s₁ s₂
| local_var {C s₁ s₂ ty x v} (h: lang_semantics C ty s₁ s₂):
  lang_semantics ([loc x . C]) ty (s₁{x ↦ v}) (s₂{x ↦ v})

/-! # Free-/

def prop.Free (P: prop): set string :=
  λ x, ∀ σ v, (P σ ↔ P (σ{x ↦ v}))

def stmt.Free (C: stmt): set string :=
  λ x, ∀ σ σ' ty v, lang_semantics C ty σ σ' ↔ lang_semantics C ty (σ{x ↦ v}) (σ'{x ↦ v})

def expression.Free (e: expression): set string :=
  λ x, ∀ σ v, e σ = e (σ{x ↦ v})

/-! # Substitute-/

def prop.substitute : string → expression → prop → prop
| x e P := λ σ, P (σ{x ↦ e σ})

notation P `[` exp `//` name `]` :=  prop.substitute name exp P

def stmt.substitute : string → expression → stmt → stmt
| x e stmt.skip                 := stmt.skip
| x e ([s ↣ e₂])                := [s ↣ λ σ, e₂ (σ{x ↦ e σ})]
| x e (stmt.non_det_assign s)   := stmt.non_det_assign s
| x e (C₁ ;; C₂)                := (stmt.substitute x e C₁) ;; (stmt.substitute x e C₂)
| x e (C₁ <+> C₂)               := (stmt.substitute x e C₁) <+> (stmt.substitute x e C₂)
| x e (C**)                     := (stmt.substitute x e C)**
| x e [loc y . C]               := if x = y then [loc x . C] else [loc y . (stmt.substitute x e C)]
| x e stmt.error                := stmt.error
| x e (stmt.assumes P)          := stmt.assumes (P[e//x])

notation C `{` exp `//` name `}` :=  stmt.substitute name exp C

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
  { exact h_H1, },
end

lemma assign_order {σ x y v₁ v₂} (Hxy: x ≠ y) :
  σ{x ↦ v₁}{y ↦ v₂} = σ{y ↦ v₂}{x ↦ v₁} :=
begin
  apply funext,
  intro z,
  by_cases h₁ : z = x,
  { finish, },
  by_cases h₂ : z = y,
  repeat{ finish, },
end

lemma assign_order_eq {σ x v₁ v₂}:
  σ{x ↦ v₁}{x ↦ v₂} = σ{x ↦ v₂} :=
begin
  apply funext,
  intro z,
  by_cases h₁ : z = x,
  repeat { finish, },
end

lemma p_thing_free {x v} {P: state -> Prop} :
  (prop.Free P) ∪ { x } ⊆ prop.Free (P{ x ↣ v }) :=
begin
  intros y hx,
  cases hx,
  {
    unfold prop.Free,
    unfold prop.Free at hx,
    intros σ v₂,
    {
      unfold p_thing,
      by_cases x = y,
      {
        split,
        repeat {
          rw h,
          rw assign_order_eq,
          exact id,
        }
      },
      {
        rw ← assign_order h,
        exact (hx (σ{x ↦ v}) v₂), 
      }
    },
  },
  {
    {
      simp at hx,
      rw hx,
      unfold prop.Free,
      intros σ v,
      split,
      repeat { unfold p_thing, finish,},
    }
  }
end

end IncLoLang