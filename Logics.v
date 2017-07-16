Require Export Lists.
Require Export Tactics.
Require Export Poly.


Definition plus_fact: Prop:= 2 + 2 = 4.

Check plus_fact.

Theorem plus_fact_is_true: plus_fact.
Proof.
  reflexivity.
Qed.

Definition is_tree(n: nat) :Prop :=
  n = 3.

Check is_tree.

Definition injective{A B} (f: A -> B) :=
  forall (x y: A), f x = f y -> x = y.

Lemma succ_inj: injective S.
Proof.
  unfold injective.
  intros.
  inversion H.
  reflexivity.
Qed.

Check @eq.

Example and_example: 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intros: forall (A B: Prop),
    A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example': 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intros.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise: forall (n m: nat),
    n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H. destruct n.
  - simpl in H. split.
    + reflexivity.
    + apply H.
  - inversion H.
Qed.

Lemma and_example2: forall (n m: nat),
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [HA HB].
  rewrite HA.
  rewrite HB.
  reflexivity.
Qed.

Lemma and_example2': forall (n m: nat),
    n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn.
  rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3: forall (n m: nat),
    n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H': n = 0 /\ m = 0).
  - apply and_exercise.
    apply H.
  - destruct H' as [Hn Hm].
    rewrite Hn.
    rewrite Hm.
    reflexivity.
Qed.

Lemma proj1: forall (P Q: Prop),
    P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

Lemma proj2: forall (P Q: Prop),
    P /\ Q -> Q.
Proof.
  intros P Q [HO HQ].
  apply HQ.
Qed.

Theorem and_commut: forall (P Q: Prop),
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ]. split.
  - apply HQ.
  - apply HP.
Qed.

Theorem and_assoc: forall (P Q R: Prop),
    P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]]. split. split.
  - apply HP.
  - apply HQ.
  - apply HR.
Qed.

Lemma or_example: forall (n m: nat),
    n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn.
    reflexivity.
  - rewrite Hm.
    apply mult_0_r.
Qed.

Lemma or_intro: forall (A B: Prop),
    A -> A \/ B.
Proof.
  intros A H HA.
  left. apply HA.
Qed.


Lemma zero_or_succ: forall (n: nat), n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_eq_0: forall (n m: nat),
    n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [|n] [|m] H.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - inversion H.
Qed.

Theorem or_commut: forall (P Q: Prop),
    P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

Module MyNot.
  Definition not (P: Prop) := P -> False.

  Notation "~ x" := (not x): type_scope.

  Check not.
End MyNot.

Theorem ex_falso_quodlibet: forall (P: Prop),
    False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not: forall (P: Prop),
    ~ P -> (forall (Q: Prop), P -> Q).
Proof.
  intros P HnP Q HP.
  unfold "~" in HnP.
  apply HnP in HP.
  destruct HP.
Qed.

Theorem zero_not_one: ~(0 = 1).
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem zero_not_one': ~(0 = 1).
Proof.
  intros H.
  inversion H.
Qed.

Theorem not_False: ~False.
Proof.
  unfold not.
  intros H.
  inversion H.
Qed.

Theorem contradiction_implies_anything: forall (P Q: Prop),
    (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HnP].
  unfold not in HnP.
  apply HnP in HP.
  inversion HP.
Qed.

Theorem double_neg: forall (P: Prop),
    P -> ~~ P.
Proof.
  intros P HP.
  unfold not.
  intros G.
  apply G.
  apply HP.
Qed.

Theorem contrapositive: forall (P Q: Prop),
    (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ.
  unfold not.
  intros HQn.
  intros HP.
  apply HQn.
  apply HPQ.
  apply HP.
Qed.

Theorem not_both_true_or_false: forall (P: Prop),
    ~ (P /\ ~P).
Proof.
  intros P. unfold not.
  intros [HP HPn].
  apply HPn. apply HP.
Qed.

Theorem not_true_is_false: forall (b: bool),
    b <> true -> b = false.
Proof.
  intros [] Hnt.
  - unfold not in Hnt.
    exfalso.
    apply Hnt.
    reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true: True.
Proof.
  apply I.
Qed.

Module MyIff.
  Definition iff (P Q: Prop) := (P -> Q) /\ (Q -> P).

  Notation "P <-> Q" := (iff P Q)
                          (at level 95, no associativity)
                        :type_scope.

End MyIff.

Theorem iff_sym: forall (P Q: Prop),
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HPQ HQP]. split.
  - apply HQP.
  - apply HPQ.
Qed.

Lemma not_true_iff_false: forall b,
    b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  - intros H. rewrite H.
    unfold not.
    intros H'.
    inversion H'.
Qed.

Theorem iff_refl: forall (P: Prop),
    P <-> P.
Proof.
  intros P. split.
  - intros H. apply H.
  - intros H. apply H.
Qed.

Theorem iff_trans: forall (P Q R: Prop),
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ HQR. split.
  - intros HP.
    apply HQR.
    apply HPQ.
    apply HP.
  - intros HR.
    apply HPQ.
    apply HQR.
    apply HR.
Qed.

Theorem or_distributes_over_and: forall (P Q R: Prop),
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP | [HQ HR]]. split.
    + left. apply HP.
    + left. apply HP.
    + split.
      * right. apply HQ.
      * right. apply HR.
  - intros [[HP | HQ] [HP' | HR]].
    + left. apply HP.
    + left. apply HP.
    + left. apply HP'.
    + right. split.
      * apply HQ.
      * apply HR.
Qed.


Require Import Coq.Setoids.Setoid.

Lemma mult_0: forall (n m: nat),
    n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc: forall (P Q R: Prop),
    P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3: forall n m p,
    n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0.
  rewrite mult_0.
  rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example: forall (n m: nat),
    n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  apply mult_0.
  apply H.
Qed.

Lemma four_is_even: exists n: nat, 4 = n + n.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2: forall n,
    (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [x H].
  exists (2+x).
  apply H.
Qed.

Theorem dist_not_exists: forall (X: Type) (P: X -> Prop),
    (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  intros [x HP].
  apply HP.
  apply H.
Qed.

Theorem dist_exists_or: forall (X: Type) (P Q: X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.

Fixpoint In {A: Type} (x: A) (l: list A) :Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1: In 4 [1;2;3;4;5].
Proof.
  simpl.
  right. right. right. left.
  reflexivity.
Qed.

Example In_example_2: forall n, In n [2;4] -> exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map: forall (A B: Type) (f: A -> B) (l: list A) (x: A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + apply IHl in H.
      right. apply H.
Qed.



Lemma In_map_iff: forall (A B: Type) (f: A -> B) (l: list A) (y: B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - intros H.
    induction l.
    + inversion H.
    + simpl in H.
      destruct H.
      * exists x. split.
        apply H.
        simpl. left. reflexivity.
      * apply IHl in H.
        simpl.
        destruct H as [x0 [H1 H2]].
        exists x0. split.
        apply H1.
        right. apply H2.
  - intros [x [H1 H2]].
    rewrite <- H1.
    apply In_map.
    apply H2.
Qed.

Lemma In_app_inff: forall A l l' (a: A),
    In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros. split.
  - induction l.
    * simpl. intros H.
      right. apply H.
    * simpl. intros [H1 | H2].
      left. left. apply H1.
      apply IHl in H2. destruct H2.
      left. right. apply H.
      right. apply H.
  - induction l.
    intros [H1 | H2].
    + inversion H1.
    + simpl.
      apply H2.
    + simpl.
      intros [[H1 | H2] | H3].
      left. apply H1.
      right. apply IHl. left. apply H2.
      right. apply IHl. right. apply H3.
Qed.

Fixpoint All {T: Type} (P: T -> Prop) (l: list T): Prop:=
  match l with
  | [] => True
  | x :: t => P x /\ All P t
  end.

Lemma All_In: forall T (P: T -> Prop) (l: list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros. split.
  - intros H. induction l.
    * simpl. apply I.
    * simpl. split.
      apply H. simpl. left. reflexivity.
      apply IHl. intros. apply H. simpl. right. apply H0.
  - intros H. intros. induction l.
    * inversion H0.
    * destruct H.
      destruct H0.
      rewrite H0 in H. apply H.
      apply IHl. apply H1.
      apply H0.
Qed.

Require Export Basics.

Definition combine_odd_even (Podd Peven: nat -> Prop): nat -> Prop:=
  fun n => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro : forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even.
  destruct (oddb n) eqn: eqn.
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd : forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n -> oddb n = true -> Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.

Theorem combine_odd_even_elim_even : forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n -> oddb n = false -> Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.

Lemma plus_comm3: forall n m p,
    n + (m + p) = (p + m) + n.
Proof.
  intros.
  rewrite plus_comm.
  rewrite (plus_comm p).
  reflexivity.
Qed.

Example lemma_application_ex : forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
  intros. destruct (proj1 _ _ (In_map_iff _ _ _ _  _) H).
  destruct H0 as [H1 H2].
  rewrite <- mult_n_O in H1.
  symmetry in H1.
  apply H1.
Qed.

Example function_equality_ex1: plus 3 = plus (pred 4).
Proof.
  reflexivity.
Qed.

Axiom functional_extensitonality: forall {X Y: Type} {f g: X -> Y},
    (forall (x: X), f x = g x) -> f = g.

Example function_equality_ex2: (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensitonality.
  intros.
  apply plus_comm.
Qed.

Fixpoint rev_append {X} (l1 l2: list X): list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l: list X): list X :=
  rev_append l [].

Lemma rev_appemd_rev: forall X (l1 l2: list X),
    rev_append l1 l2 = rev l1 ++ l2.
Proof.
  intros.
  induction l1.
  - reflexivity.
  - simpl.
    rewrite <- app_assoc.
Admitted.


Lemma tr_rev_corrct: forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensitonality.
  intro l. induction l.
  - reflexivity.
  - simpl. rewrite <- IHl. unfold tr_rev.
    SearchAbout (rev _ ++ _).
Admitted.

Theorem evenb_double: forall k, evenb (double k) = true.
Proof.
  intros. induction k as [|k IHk].
  - reflexivity.
  - simpl. apply IHk.
Qed.

Theorem evenb_double_conv: forall n,
    exists k, n = if evenb n then double k else S (double k).
Proof.
  intros. induction n.
  - simpl. exists 0. reflexivity.
  - rewrite evenb_S.
    destruct (evenb n) eqn: miao.
    * simpl.
      destruct IHn.
      exists x.
      rewrite H.
      reflexivity.
    * simpl.
      destruct IHn.
      exists (S x).
      rewrite H.
      reflexivity.
Qed.

Theorem evenb_bool_prop: forall n,
    evenb n = true <-> exists k, n = double k.
Proof.
  intros. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite H in Hk.
    exists k.
    rewrite Hk.
    reflexivity.
  - intros [x Hk].
    rewrite Hk.
    apply evenb_double.
Qed.

Theorem beq_nat_true_iff: forall n1 n2: nat,
    beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros. split.
  - apply beq_nat_true.
  - intros H.
    rewrite H.
    rewrite <- beq_nat_relf.
    reflexivity.
Qed.

Example evenb_1000: exists k, 1000 = double k.
Proof.
  exists 500.
  reflexivity.
Qed.

Example event_1000': exists k, 1000 = double k.
Proof.
  apply evenb_bool_prop.
  reflexivity.
Qed.

Lemma andb_true_iff: forall b1 b2: bool,
    b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H.
    destruct b1.
    destruct b2.
    * split. reflexivity. reflexivity.
    * inversion H.
    * inversion H.
  - intros [H1 H2].
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Lemma orb_comm: forall b1 b2: bool,
    b1 || b2 = b2 || b1.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma orb_true_iff: forall b1 b2: bool,
    b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H.
    destruct b1.
    destruct b2.
    * left. reflexivity.
    * left. reflexivity.
    * right. apply H.
  - intros [H1 | H2].
    rewrite H1. reflexivity.
    rewrite H2. apply orb_comm.
Qed.

Theorem beq_nat_false: forall x y: nat,
    beq_nat x y = false -> x <> y.
Proof.
  intros x y H. unfold not.
  intros N. rewrite N in H.
  rewrite <- beq_nat_relf in H. inversion H.
Qed.
    
Theorem beq_nat_false_iff: forall x y: nat,
    beq_nat x y = false <-> x <> y.
Proof.
  intros x y. split.
  - apply beq_nat_false.
  - unfold not.
    induction x.
    induction y.
    * intros H.
Admitted.

Fixpoint beq_list {A: Type} (beq: A -> A -> bool)
         (l1 l2: list A): bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ => false
  | _, [] => false
  | a :: l1', b :: l2' => andb (beq a b) (beq_list beq l1' l2')
  end.

Lemma beq_list_true_iff: forall A (beq: A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) -> (forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2).
Proof.
  intros A beq H l1 l2. induction l1. induction l2.
  - simpl. split.
    * intros H1. reflexivity.
    * intros H1. reflexivity.
  - simpl. split.
    * intros H1. inversion H1.
    * intros H1. inversion H1.
  - Admitted.

Fixpoint forallb {X: Type} (test: X -> bool) (l: list X): bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff: forall X test (l: list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros. split. induction l.
  - simpl. intros H. apply I.
  - simpl. intros H. apply andb_true_iff in H. destruct H. split.
    apply H.
    apply IHl.
    apply H0.
  - intros H.
Admitted.

Definition excluded_middle:= forall P: Prop,
    P \/ ~P.

Theorem restricted_excluded_middle: forall P b,
    (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. apply H. reflexivity.
  - right. rewrite H. intros contra.
    inversion contra.
Qed.

Theorem restricted_excludede_middle_eq: forall (n m: nat),
    n = m \/ n <> m.
Proof.
  intros.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

Theorem excluded_middle_irrefutable: forall (P: Prop),
    ~~(P \/ ~P).
Proof.
  intros. unfold not.
  intros. apply H.
  right. intros. apply H. left. apply H0.
Qed.