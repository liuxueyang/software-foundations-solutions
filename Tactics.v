Require Export Poly.

Theorem silly1: forall (n m o p: nat),
    n = m -> [n;o] = [n;p] -> [n;o] = [m;p].
Proof.
  intros n m o p H1 H2.
  rewrite <- H1.
  apply H2.
Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a: forall (n m: nat),
    (n,n) = (m,m) -> (forall (q r: nat), (q,q) = (r,r) -> [q] = [r]) -> [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex:
  (forall n, evenb n = true -> oddb (S n) = true) -> evenb 3 = true -> oddb 4 = true.
Proof.
  intros H.
  apply H.
Qed.

Theorem silly3_firsttry: forall (n: nat), true = beq_nat n 5 -> beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  symmetry.
  apply H.
Qed.

Theorem rec_exercise1: forall (l l': list nat),
    l = rev l' -> l' = rev l.
Proof.
  intros l1 l' H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

Example trans_eq_example: forall (a b c d e f: nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem trans_eq: forall (X: Type) (n m o: X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Example trans_eq_example': forall (a b c d e f: nat),
    [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  apply trans_eq with [c;d].
  apply H1.
  apply H2.
Qed.

Example trans_eq_exercise: forall (n m o p: nat),
    m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  apply trans_eq with (n+p).
  reflexivity.
  rewrite -> H2.
  apply H1.
Qed.



Theorem s_injective: forall (n m: nat),
    S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1: forall (n m o: nat),
    [n;m] = [o;o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2: forall (n m: nat),
    [n] = [m] -> n = m.
Proof.
  intros n m H.
  inversion H as [Hnm].
  reflexivity.
Qed.

Example inversion_ex3: forall (X: Type) (x y z: X) (l j: list X),
    x :: y :: l = z :: j -> y :: l = x :: j -> x = y.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
  inversion H2.
  rewrite -> H0.
  reflexivity.
Qed.

Theorem beq_nat_0_l: forall n,
    beq_nat 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [|n'].
  - intros H.
    reflexivity.
  - intros H.
    inversion H.
Qed.

Theorem inversion_ex4: forall (n: nat),
    S n = O -> 2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem inversion_ex5: forall (n m: nat),
    false = true -> [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.

Example inversion_ex6: forall (X: Type) (x y z: X) (l j: list X),
    x :: y :: l = [] -> y :: l = z :: j -> x = z.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
Qed.

Theorem f_equal: forall (A B: Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof.
  intros  A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

Theorem S_inj: forall (n m: nat) (b: bool),
    beq_nat (S n) (S m) = b -> beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly3': forall (n: nat),
    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
    true = beq_nat n 5 ->
    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

Theorem plus_n_n_injective: forall n m,
    n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [|n'].
  - intros m H.
    destruct m.
    * reflexivity.
    * inversion H.
  - intros m H.
Admitted.

Theorem double_injective: forall n m,
    double n = double m -> n = m.
Proof.
  intros n.
  induction n as [|n'].
  - intros m H.
    destruct m.
    + reflexivity.
    + inversion H.
  - intros m H.
    destruct m.
    + inversion H.
    + apply f_equal.
      apply IHn'.
      inversion H.
      reflexivity.
Qed.

Theorem beq_nat_true: forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros m H.
    destruct m.
    * reflexivity.
    * inversion H.
  - intros m H.
    destruct m.
    * inversion H.
    * apply f_equal.
      apply IHn.
      inversion H.
      reflexivity.
Qed.

Theorem double_injective_take2_FAILED: forall n m,
    double n = double m -> n = m.
Proof.
  intros n m.
  induction m as [|m'].
  - intros eq.
    destruct n as [|n'].
    + reflexivity.
    + inversion eq.
  - intros eq.
    destruct n as [|n'].
    + inversion eq.
    + apply f_equal.
Abort.

Require Export Lists.


Theorem beq_id_true: forall x y,
    beq_id x y = true -> x = y.
Proof.
  intros [n] [m].
  simpl.
  intros H.
  apply f_equal.
  apply beq_nat_true in H.
  apply H.
Qed.

Theorem nth_error_after_last: forall (n: nat) (X: Type) (l: list X),
    length l = n -> nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l.
  - intros.
    reflexivity.
  - intros.
Admitted.

Definition square n := n * n.

Lemma square_mult: forall n m,
    square (n * m) = square n * square m.
Proof.
  intros.
  unfold square.
  rewrite mult_assoc.
  assert (H: n * m * n = n * n * m).
  - rewrite mult_comm.
    rewrite mult_assoc.
    reflexivity.
  - rewrite H.
    rewrite mult_assoc.
    reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1: forall m,
    foo m + 1 = foo (m + 1) + 1.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Definition bar (x: nat) :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2: forall m,
    bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n: nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false: forall (n: nat),
    sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (beq_nat n 3).
  - reflexivity.
  - destruct (beq_nat n 5).
    + reflexivity.
    + reflexivity.
Qed.

Theorem combine_split: forall X Y (l: list (X * Y)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  - intros l1 l2 eq.
    inversion eq.
    reflexivity.
  - simpl.
    destruct (split l).
    intros l2 l3 eq.
Admitted.

Definition sillyfun1(n: nat) :bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem sillyfun1_odd: forall (n: nat),
    sillyfun1 n = true -> oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn: Heqe3.
  - apply beq_nat_true in Heqe3.
    rewrite -> Heqe3.
    reflexivity.
  - destruct (beq_nat n 5) eqn: Heqe5.
    * apply beq_nat_true in Heqe5.
      rewrite -> Heqe5.
      reflexivity.
    * inversion eq.
Qed.

Theorem bool_fn_applied_thrice: forall (f: bool -> bool) (b: bool),
    f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  - destruct (f true) eqn: Hft.
    + rewrite Hft.
      apply Hft.
    + destruct (f false) eqn: Hff.
      * apply Hft.
      * apply Hff.
  - destruct (f false) eqn: Hff.
    + destruct (f true) eqn: Htt.
      * apply Htt.
      * apply Hff.
    + rewrite Hff.
      apply Hff.
Qed.

Theorem beq_nat_sym: forall (n m: nat),
    beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n.
  - intros m.
    induction m.
    + reflexivity.
    + unfold beq_nat.
      reflexivity.
  - intros m.
    induction m.
    + unfold beq_nat.
      reflexivity.
    + simpl.
      apply IHn.
Qed.

Theorem beq_nat_trans: forall (n m p: nat),
    beq_nat n m = true ->
    beq_nat m p = true ->
    beq_nat n p = true.
Proof.
  intros n m p H1 H2.
  apply beq_nat_true in H1.
  apply beq_nat_true in H2.
  rewrite H1.
  rewrite H2.
  symmetry.
  apply beq_nat_relf.
Qed.

Definition split_combine_statement: Prop :=
  forall {X Y: Type} (l1: list X) (l2: list Y),
    length l1 = length l2 ->
    split (combine l1 l2) = (l1, l2).

Theorem split_combine: split_combine_statement.
Proof.
  intros X Y l1.
  induction l1.
  - intros l2 H.
    induction l2.
    + reflexivity.
    + simpl in H.
      destruct (length l2).
      * inversion H.
      * inversion H.
  - intros l2 H.
    induction l2.
    + simpl in H.
      destruct (length l1).
      * inversion H.
      * inversion H.
    + Admitted.


  