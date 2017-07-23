(* 2017年07月16日 星期日 19时40分05秒 *)

Check True.

Check False.

Check (3 + 4).

Check (3, 3 < 5).

Check (fun x : nat => x < 3 \/ x >= 3).

Check (forall x : nat, x < 3 \/ (exists y : nat, x = y + 3)).

Inductive day : Type :=
| Monday : day
| Tuesday : day
| Wendsday : day
| Thursday : day
| Friday : day
| Saturday : day
| Sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
  | Monday => Tuesday
  | Tuesday => Wendsday
  | Wendsday => Thursday
  | Thursday => Friday
  | Friday => Saturday
  | Saturday => Sunday
  | Sunday => Monday
  end.

Compute (next_weekday Monday).

Compute (next_weekday Sunday).

Example test_next_weekday :
  (next_weekday (next_weekday Saturday)) = Monday.
Proof. simpl. reflexivity. Qed.

Example test_next_weekday_error :
  (next_weekday Saturday) = Sunday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5 : (false || false || true) = true.
Proof. simpl. reflexivity. Qed.

(* Mon Jul 17 13:55:21 2017 *)
(* Exercise: 1 star (nandb) *)

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | false => true
  | true => (negb b2)
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1 star (andb3) *)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | true => (andb b2 b3)
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Check true.

Check (negb true).

Check negb.

(* Mon Jul 17 20:40:17 2017 *)

Module Nat.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End Nat.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Check O.
Check (S O).
Check (S (S O)).
Compute (minustwo 4).
Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => (evenb n')
  end.

Compute (evenb 3).
Compute (evenb 4).

Fixpoint oddb (n : nat) : bool :=
  match n with
  | O => false
  | S O => true
  | S n' => evenb n'
  end.

Definition oddb1 (n : nat) : bool := negb (evenb n).

Example test_oddb1 : oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2 : oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module Type NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => plus n' (S m)
    end.

  Compute (plus 3 4).

  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S O => m
    | S n' => plus m (mult n' m)
    end.

  Compute (mult 2 3).
  Compute (mult 1 101).

  Example test_mult1 : (mult 3 2) = 6.
  Proof. simpl. reflexivity. Qed.

  Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | O, _ => O
    | _, O => n
    | S n', S m' => minus n' m'
    end.

  Compute (minus 3 2).
  Compute (minus 2 3).
End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match base, power with
  | O, _ => O
  | _, O => S O
  | _, S power' => mult base (exp base power')
  end.

Compute (exp 2 3).
Compute (exp 3 0).
Compute (exp 0 10).

(* Exercise: 1 star (fractorial) *)

(* 2017年07月17日 星期一 21时51分39秒 *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Compute (factorial 5).

Example test_factorial1 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2 : (factorial 5) = 120.
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                    : nat_scope.

Notation "x * y" := (mult x y)
                      (at level 40, left associativity)
                    : nat_scope.

Check ((2 + 3) * 4).

Fixpoint beq_nat (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, S _ => false
  | S _, O => false
  | S n', S m' => beq_nat n' m'
  end.

Compute (beq_nat 3 3).
Compute (beq_nat 3 4).

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
           | O => false
           | S m' => leb n' m'
           end
  end.

Compute (leb 3 2).
Compute (leb 2 3).

(* Exercise: 1 star (blt_nat) *)
Definition blt_nat (n m : nat) : bool := andb (leb n m) (negb (beq_nat n m)).

Compute (blt_nat 3 4).
Compute (blt_nat 4 3).
Compute (blt_nat 4 4).

Example test_blt_nat1 : (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2 : (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3 : (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

(* ==================== *)
(* Proof by Simplification *)
(* ==================== *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. simpl. reflexivity. Qed.

(* TODO ??? *)
(* Theorem mult_1_l : forall n : nat, 1 * n = n. *)
(* Proof. *)
(*   intros n. reflexivity. Qed. *)

(* Theorem plus_n_O : forall n : nat, n = n + 0. *)
(* Proof. *)
(*   intros n. simpl. reflexivity. *)

(* ==================== *)
(* Proof by Rewriting *)
(* ==================== *)

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.

Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity. Qed.

(* Exercise: 1 star (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.

Proof.
  intros n m o.
  intros H H1.
  rewrite -> H.
  rewrite <- H1.
  reflexivity. Qed.

Theorem mult_O_plus : forall n m : nat,
    (0 + n) * m = n * m.

Proof.
  intros n m.
  rewrite plus_O_n.
  reflexivity. Qed.

(* Exercise: 2 stars (mult_S_1) *)
Theorem mult_S_l : forall n m : nat,
    m = S n ->
    m * (1 + n) = m * m.

Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity. Qed.

(* ==================== *)
(* Proof by Case Analysis *)
(* ==================== *)

Theorem plus_1_neq_O : forall n : nat,
    beq_nat (n + 1) 0 = false.

Proof.
  intros n. destruct n as [| n'].
  - reflexivity.
  - reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.

Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.

