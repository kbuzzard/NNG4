import Game.Metadata
import Game.MyNat.AdvAddition
import Game.Levels.Addition
import Game.Tactic.Use
import Game.Levels.Multiplication
import Game.Levels.AdvAddition
--import Mathlib.Tactic

open MyNat

theorem add_add_add_comm( a b c d : ℕ ) : a + b + (c + d) = a + c + (b + d) := by
rw[add_assoc]
rw[← add_assoc b c d]
rw[add_comm b c]
rw[add_assoc c b d]
rw[← add_assoc]
rfl

theorem add_left_comm( a b c : ℕ) : a + (b + c) = b + (a + c) := by
rw[← add_assoc]
rw[add_comm a b]
rw[add_assoc]
rfl

def IsEven (n:ℕ):Prop:= ∃t:ℕ, n = t + t
def IsOdd (n:ℕ):Prop:= ∃t:ℕ, n = t + t + 1



theorem eq_zero_or_add_one (t : ℕ) : t = 0 ∨ ∃ n, t = n + 1 := by
  induction t with d _
  · left
    rfl
  · right
    use d
    rw [succ_eq_add_one]
    rfl

theorem IsOdd_add_IsOdd( a b : ℕ) (ha : IsOdd a) (hb : IsOdd b) : IsEven ( a + b) := by
  rw[IsOdd] at ha
  rw[IsOdd] at hb
  rw[IsEven]
  rcases ha with ⟨t, hat⟩
  rcases hb with ⟨s, has⟩
  rw[hat, has]
  use t + s + 1
  simp only [add_assoc]
  rw[add_left_comm t 1]
  rw[add_left_comm t s]
  rw[add_left_comm 1 s]
  rfl


theorem IsEven_add_IsEven( a b : ℕ) (ha : IsEven a) (hb : IsEven b) : IsEven ( a + b) := by
rw[IsEven] at ha
rw[IsEven] at hb
rw[IsEven]
rcases ha with ⟨t, hat⟩
rcases hb with ⟨s, has⟩
rw[hat, has]
rw[← add_assoc]
rw[add_comm]
rw[← add_assoc]
rw[← add_assoc]
rw[add_right_comm]
rw[add_assoc]
use  s + t

theorem IsEven_add_IsOdd( a b : ℕ ) (ha : IsEven a) (hb : IsOdd b) : IsOdd ( a + b ) := by
rw[IsEven] at ha
rw[IsOdd] at hb
rw[IsOdd]
rcases ha with ⟨t, hat⟩
rcases hb with ⟨s, has⟩
rw[hat, has]
rw[← add_assoc]
use t + s
rw[← add_assoc]
rw[add_add_add_comm]
simp only [add_assoc]



theorem IsOdd_add_IsEven( a b : ℕ ) (ha : IsOdd a) (hb : IsEven b) : IsOdd ( a + b) := by
rw[IsOdd]
rw[IsOdd] at ha
rw[IsEven] at hb
rcases ha with ⟨s, rfl⟩
rcases hb with ⟨m, rfl⟩
use s + m
rw[add_left_comm]
simp only [add_assoc]
rw[add_comm 1 m]
rw[add_left_comm]
rfl

theorem IsEven_mul( a b : ℕ ) (ha: IsEven a) : IsEven ( a * b ) := by
rw[IsEven] at ha
rw[IsEven]
rcases ha with ⟨s, has⟩
rw[has]
rw[add_mul]
use s * b

theorem IsOdd_mul_IsOdd( a b : ℕ ) (ha : IsOdd a) (hb : IsOdd b) : IsOdd ( a * b) := by
rw[IsOdd] at ha
rw[IsOdd] at hb
rw[IsOdd]
rcases ha with ⟨t, hat⟩
rcases hb with ⟨s, has⟩
rw[has, hat]
rw[add_mul]
rw[add_mul]
rw[one_mul] --new code
use t* (s + s + 1) + s
simp only [add_assoc]
rw[add_left_comm s (t * (s + (s + 1)))]
rfl

theorem zero_IsEven : IsEven ( 0 ) := by
rw[IsEven]
use 0
rw[add_zero]
rfl


theorem zero_not_IsOdd : ¬ IsOdd ( 0 ) := by
rw[IsOdd]
intro h
rcases h with ⟨s, hs⟩
rw[add_one_eq_succ] at hs
apply zero_ne_succ (s + s)
exact hs

theorem succ_IsEven_IsOdd( a : ℕ ) (ha :IsEven a) : IsOdd ( succ a ) := by
rw[IsEven] at ha
rcases ha with ⟨s, has⟩
rw[IsOdd]
rw[has]
rw[succ_eq_add_one]
use s


theorem succ_IsOdd_IsEven( a : ℕ ) (ha : IsOdd a) : IsEven ( succ a) := by
rw[IsOdd] at ha
rcases ha with ⟨s, has⟩
rw[IsEven]
rw[has]
rw[succ_eq_add_one]
use s + 1
rw[add_add_add_comm]
simp only [add_assoc]

theorem IsOdd_succ_IsEven(a : ℕ ) (ha : IsOdd a) : ∃b:ℕ, (IsEven b) ∧ (a = succ b) := by
rw[IsOdd] at ha
rcases ha with ⟨s, has⟩
rw[has]
use s + s
constructor
rw[IsEven]
use s
rw[succ_eq_add_one]
rfl

theorem IsEven_zero_or_succ_IsOdd(a : ℕ )
 (ha : IsEven a) : a = 0 ∨ ∃b:ℕ, (IsOdd b) ∧ (a = succ b) := by
 rw[IsEven] at ha
 rcases ha with ⟨s, has⟩
 rcases s
 left
 rw[has]
 show 0 + 0 = 0
 rw[add_zero]
 rfl
 right
 use a_1 + succ a_1
 constructor
 rw[IsOdd]
 rw[succ_eq_add_one]
 use a_1
 rw[← add_assoc]
 rfl
 rw[has]
 rw[succ_add]
 rfl

theorem IsEven_or_IsOdd(a : ℕ ) : (IsOdd a ) ∨ (IsEven a) := by
induction a with d hd
right
apply zero_IsEven
rcases hd
right
apply succ_IsOdd_IsEven
apply h
left
apply succ_IsEven_IsOdd
apply h

theorem IsOdd_implies_succ_IsEven(a: ℕ ) : (IsOdd a) → ∃b:ℕ, (IsEven b) ∧ (a = succ b) := by
intro h
apply IsOdd_succ_IsEven
exact h

theorem IsEven_succ_implies_IsOdd(a : ℕ ) : (IsEven (succ a)) → (IsOdd a) := by
intro h
rw[IsEven] at h
rw[IsOdd]
rw[succ_eq_add_one] at h
rcases h with ⟨ s, hs ⟩
rcases eq_zero_or_add_one s
exfalso
rw[h] at hs
rw[add_zero] at hs
rw[add_one_eq_succ] at hs
apply succ_ne_zero a
exact hs
rcases h with ⟨ v, hv ⟩
rw[hv] at hs
rw[add_one_eq_succ] at hs
use v
apply succ_inj
rw[hs]
rw[succ_eq_add_one]
rw[← add_assoc]
congr 1
rw[add_comm]
rw[add_assoc]
rfl

theorem IsOdd_succ_implies_IsEven(a : ℕ ) : (IsOdd (succ a)) → (IsEven a) := by
intro h
rw[IsOdd] at h
rw[IsEven]
rcases h with ⟨ s, hs ⟩
use s
apply succ_inj
rw[add_one_eq_succ] at hs
exact hs

theorem IsEven_implies_zero_or_succ_IsOdd(a : ℕ ) :
(IsEven a) → (a = 0) ∨ ∃b:ℕ, (IsOdd b) ∧ (a = succ b):= by
intro h
apply IsEven_zero_or_succ_IsOdd
exact h

theorem not_IsEven_and_IsOdd(a : ℕ ) : ¬( IsOdd a ∧ IsEven a) := by
induction a with d hd
intro h
apply zero_not_IsOdd
rcases h
apply left
intro h
apply hd
constructor
rcases h
apply IsEven_succ_implies_IsOdd
exact right
rcases h
apply IsOdd_succ_implies_IsEven
exact left

