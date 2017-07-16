Require Export Basics.

Compute (evenb 2).

Theorem plus_O_firstry: forall n:nat, n = n + O.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem minus_diag: forall n:nat, minus n n = 0.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem mult_0_r: forall n:nat, n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_n_Sm: forall n m:nat, S (n + m) = n + S m.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl.
    intros m.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_comm: forall n m:nat, n + m = m + n.
Proof.
  induction n as [|n' IHn'].
  - induction m as [|m IHm'].
    * reflexivity.
    * simpl.
      rewrite <- IHm'.
      simpl.
      reflexivity.
  - intros m.
    simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc: forall n m p:nat, n + (m + p) = (n + m) + p.
Proof.
  induction n as [|n' IHn'].
  - intros m p.
    simpl.
    reflexivity.
  - intros m p.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Fixpoint double (n:nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Notation "x + y" := (plus x y) (at level 50, left associativity) :nat.

Notation "x * y" := (mult x y) (at level 40, left associativity) :nat.

Lemma double_plus: forall n:nat, double n = n + n.
Proof.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.



Theorem evenb_S: forall n: nat, evenb (S n) = negb (evenb n).
Proof.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - rewrite -> IHn'.
    rewrite -> negb_involutive.
    simpl.
    reflexivity.
Qed.

Theorem mult_0_plus': forall n m: nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
  - reflexivity.
  - rewrite -> H.
    reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q: nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (n + m = m + n) as H.
  - rewrite plus_comm.
    reflexivity.
  - rewrite H.
    reflexivity.
Qed.

Theorem plus_swap: forall n m p: nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (n + m = m + n) as H.
  - rewrite -> plus_comm.
    reflexivity.
  - rewrite -> H.
    reflexivity.
Qed.

Theorem mult_n_Sm: forall n m: nat, n * S m = n + n * m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_swap.
    reflexivity.
Qed.

Theorem mult_comm: forall m n: nat, m * n = n * m.
Proof.
  induction m as [|m' IHm'].
  - intros n.
    rewrite -> mult_0_r.
    reflexivity.
  - intros n.
    simpl.
    rewrite -> IHm'.
    rewrite -> mult_n_Sm.
    reflexivity.
Qed.

Theorem leb_refl: forall n:nat, true = leb n n.
Proof.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem zero_nbeq_S: forall n: nat, beq_nat O (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r: forall b:bool, andb b false = false.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem plus_ble_compat_l: forall n m p: nat,
    leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p H.
  induction p as [|p' IHp'].
  - simpl.
    rewrite <- H.
    reflexivity.
  - simpl.
    rewrite <- IHp'.
    reflexivity.
Qed.

Theorem S_nbeq_0: forall n:nat, beq_nat (S n) 0 = false.
Proof.
  intros [].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem mult_1_l: forall n:nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Theorem all3_spec: forall b c:bool,
    orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r: forall n m p: nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc: forall n m p: nat,
    n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

Theorem beq_nat_relf: forall n: nat,
    true = beq_nat n n.
Proof.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem plus_swap': forall n m p: nat,
    n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  - reflexivity.
  - rewrite -> plus_comm.
    reflexivity.
Qed.

Inductive bin: Type :=
| Z : bin
| T : bin -> bin
| TP : bin -> bin.

Fixpoint incr(b: bin): bin :=
  match b with
  | Z => TP Z
  | T n => TP n
  | TP n => T (incr n)
  end.

Fixpoint bin_to_nat(b: bin): nat :=
  match b with
  | Z => O
  | T n => mult (bin_to_nat n) (S (S O))
  | TP n => S (mult (bin_to_nat n) (S (S O)))
  end.

Example test_bin_incr1: bin_to_nat (incr Z) = 1.
Proof.
  reflexivity.
Qed.

Example test_bin_incr2: bin_to_nat (incr (T Z)) = 1.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr3: bin_to_nat (incr (TP Z)) = 2.
Proof.
  reflexivity.
Qed.

Example test_bin_incr4: bin_to_nat (incr (T (T Z))) = 1.
Proof.
  reflexivity.
Qed.

Example test_bin_incr5: bin_to_nat (incr (TP (TP Z))) = 4.
Proof.
  reflexivity.
Qed.

Theorem bin_to_nat_pres_incr: forall b: bin,
    bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  induction b as [|b IHb |c IHc].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHc.
    reflexivity.
Qed.

Fixpoint nat_to_bin(n: nat): bin :=
  match n with
  | O => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_to_bin_to_nat: forall n: nat,
    bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'.
    reflexivity.
Qed.


Compute (nat_to_bin 1).
Compute (nat_to_bin 2).
Compute (nat_to_bin 3).
Compute (nat_to_bin 4).
Compute (nat_to_bin 5).
Compute (nat_to_bin 6).

Theorem inverse_normalize: forall b: bin,
    nat_to_bin (bin_to_nat b) = b.
Proof.
  intros b.
  induction b as [|b' IHb' |b' IHb'].
  - simpl.
    reflexivity.
  - simpl.
Admitted.

