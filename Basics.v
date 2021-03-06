Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday(d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  simpl. reflexivity.
Qed.

Inductive bool : Type :=
| true: bool
| false: bool.

Definition negb (b: bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb2: (orb false false) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb3: (orb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb4: (orb true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Infix "&&" := andb.
Infix "||" := orb.

Example test_orb5 : false || false || true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Definition nandb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => match b2 with
            | true => false
            |false => true
            end
  | false => true
  end.


Example test_nandb1: (nandb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Definition andb3 (b1: bool) (b2: bool) (b3 :bool) : bool :=
  match b1 with
  | true => andb b2 b3
  | false => false
  end.

Example test_andb31: (andb3 true true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb33: (andb3 true false true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Module Playground1.
  Inductive nat: Type :=
  | O : nat
  | S : nat -> nat.

  Definition pred (n: nat) :nat :=
    match n with
    | O => O
    | S n' => n'
    end.

End Playground1.

Definition minustwo (n: nat) :nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Fixpoint evenb (n: nat) :bool:=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n: nat): bool :=
  negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_oddb2: oddb 4 = false.
Proof.
  simpl.
  reflexivity.
Qed.

Module Playground2.
  Fixpoint plus (n: nat) (m: nat) :nat :=
    match n with
    | O => m
    | S n'=> S (plus n' m)
    end.

  Fixpoint mult (n m: nat) :nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.

  Example test_mult1: (mult 3 3) = 9.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint minus (n m:nat) :nat :=
    match n, m with
    | O, _ => O
    | S _, O => n
    | S n', S m' => minus n' m'
    end.

End Playground2.

Fixpoint exp (base power: nat) :nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n: nat) :nat :=
  match n with
  | O => S O
  | S n' => mult (factorial n') (S n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_l: forall n: nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_l: forall n: nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_n_O: forall n: nat, n = n + O.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite <- IHn. reflexivity.
Qed.

Theorem plus_id_example: forall n m:nat, n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_exercise: forall n m o:nat, n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem mult_0_plus: forall n m: nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

Theorem mult_S_1: forall n m:nat, m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> plus_1_l.
  rewrite <- H.
  reflexivity.
Qed.

Fixpoint beq_nat (n m:nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint leb (n m: nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Fixpoint blt_nat (n m: nat): bool :=
  match n with
  | O => match m with
         | O => false
         | S n' => true
         end
  | S n' => match m with
            | O => false
            | S m' => blt_nat n' m'
            end
  end.

Theorem plus_1_neq_0_firsttry: forall n: nat, beq_nat (n + 1) 0 = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_1_neq_0: forall n:nat, beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [| n'].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem negb_involutive: forall b:bool, negb (negb b) = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative: forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb_commutative': forall b c:bool, andb b c = andb c b.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange: forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d.
  destruct b.
  - destruct c.
    + destruct d.
      * reflexivity.
      * reflexivity.
    + destruct d.
      * reflexivity.
      * reflexivity.
  - destruct c.
    + destruct d.
      * reflexivity.
      * reflexivity.
    + destruct d.
      * reflexivity.
      * reflexivity.
Qed.

Theorem plus_1_neq_0': forall n: nat, beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'': forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_true_elim2: forall b c: bool, andb b c = true -> c = true.
Proof.
  intros.
  induction b.
  - simpl in H. apply H.
  - inversion H.
Qed.

Theorem zero_nbeq_plus_1: forall n:nat, beq_nat 0 (n + 1) = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint plus' (n: nat) (m: nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus' n' m)
  end.

Theorem identity_fn_applied_twice:
  forall (f: bool -> bool), (forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros [].
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
  - rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem andb_eq_orb:
  forall (b c: bool), (andb b c = orb b c) -> b = c.
Proof.
  intros [] c.
  - simpl.
    intros H.
    rewrite -> H.
    reflexivity.
  - simpl.
    intros H.
    rewrite -> H.
    reflexivity.
Qed.
