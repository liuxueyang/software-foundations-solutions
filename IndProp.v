Require Export Poly.
Require Export Logics.


Inductive ev: nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall (n: nat), ev n -> ev (S (S n)).

Theorem ev_4: ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_plus4: forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros H.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Require Export Tactics.

Theorem ev_double: forall n,
    ev (double n).
Proof.
  intros n. induction n.
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.

Theorem ev_minus2: forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [|n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem ev_minus2': forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [|n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev: forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  apply E'.
Qed.

Theorem one_not_even: ~ ev 1.
Proof.
  intros H.
  inversion H.
Qed.

Theorem SSSSen_even: forall n,
    ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

Theorem even5_nonsense:
  ev 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

Lemma ev_even: forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E'].
  - exists 0. reflexivity.
  - destruct IHE'.
    exists (S x).
    rewrite H.
    reflexivity.
Qed.

Lemma ev_even_firstty: forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [|n' E'].
  - exists 0. reflexivity.
  - simpl.
    assert (l: (exists k', n' = double k') -> (exists k, S (S n') = double k)).
    * intros [k' Hk'].
      rewrite Hk'.
      exists (S k').
      reflexivity.
    * apply l.
      apply ev_even in E'.
      destruct E'.
      exists x.
      apply H0.
Qed.

Theorem ev_even_iff: forall n,
    ev n <-> exists k, n = double k.
Proof.
  intros. split.
  - apply ev_even.
  - intros [k Hk].
    rewrite Hk. apply ev_double.
Qed.

Theorem double_sum: forall n m, double (n + m) = double n + double m.
Proof.
  intros n m. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem ev_sum: forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  apply ev_even in Hn.
  apply ev_even in Hm.
  destruct Hn as [n' Hn].
  destruct Hm as [m' Hm].
  rewrite Hn.
  rewrite Hm.
  rewrite <- double_sum.
  apply ev_double.
Qed.

Inductive ev': nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev: forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros E. induction E.
    * apply ev_0.
    * apply ev_SS. apply ev_0.
    * apply ev_sum. apply IHE1. apply IHE2.
  - intros E. induction E.
    * apply ev'_0.
    * assert (l: forall n, ev' (S (S n)) = ev' (2 + n)).
    + intros [].
      reflexivity.
      reflexivity.
    + rewrite l.
      apply ev'_sum. apply ev'_2. apply IHE.
Qed.

Theorem ev_ev__ev: forall n m,
    ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H1 H2. induction H2.
  - apply H1.
  - apply IHev. simpl in H1. apply evSS_ev in H1. apply H1.
Qed.

Theorem ev_plus_plus: forall n m p,
    ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p Hnm Hnp.
  apply ev_ev__ev with (n := n + n).
  - rewrite plus_swap.
    rewrite plus_assoc.
    rewrite plus_swap.
    rewrite plus_assoc.                  
    rewrite <- plus_assoc.
    apply ev_sum.
    apply Hnm. apply Hnp.
  - rewrite <- double_plus.
    apply ev_double.
Qed.

Module Playground.

  Inductive le: nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, le n m -> le n (S m).

  Notation "n <= m" := (le n m).

  Theorem test_le1: 3 <= 3.
  Proof.
    apply le_n.
  Qed.

  Theorem test_le2: 3 <= 6.
  Proof.
    apply le_S. apply le_S. apply le_S. apply test_le1.
  Qed.

  Theorem test_le3: (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intros.
    inversion H.
    inversion H2.
  Qed.

End Playground.

Definition lt(n m: nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of: nat -> nat -> Prop :=
| sq : forall n: nat, square_of n (n * n).

Inductive next_nat: nat -> nat -> Prop :=
| nn : forall n: nat, next_nat n (S n).

Inductive next_even: nat -> nat -> Prop :=
| ne_1 : forall n, ev (S n) -> next_even n (S n)
| ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Inductive total_relation: nat -> nat -> Prop :=
| tot: forall n m: nat, total_relation n m.

Inductive empty_relation: nat -> nat -> Prop :=.

Lemma Sn_le_m__n_le_m: forall n m,
    S n <= m -> n <= m.
Proof.
  intros n m H. induction H.
  - apply le_S. apply le_n.
  - apply le_S. apply IHle.
Qed.

Lemma Sn_le_Sm__n_le_m: forall n m,
    S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - reflexivity.
  - apply Sn_le_m__n_le_m. apply H1.
Qed.

Lemma le_trans: forall n m o, m <= n -> n <= o -> m <= o.
Proof.
  intros n m o H1 H2. induction H1.
  - apply H2.
  - apply IHle. apply Sn_le_m__n_le_m. apply H2.
Qed.

Lemma O_le_n: forall n, 0 <= n.
Proof.
  intros n. induction n.
  - apply le_n.
  - apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm: forall n m,
    n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Theorem le_plus_l: forall a b,
    a <= a + b.
Proof.
  intros a b. induction a.
  - simpl. apply O_le_n.
  - rewrite plus_Sn_m.
    apply n_le_m__Sn_le_Sm.
    apply IHa.
Qed.

Theorem plus_lt: forall n1 n2 m,
    n1 + n2 < m -> n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m. unfold lt. intros H. split.
  - induction n2.
    * rewrite <- plus_n_O in H. apply H.
    * apply IHn2.
      rewrite <- plus_n_Sm in H.
      apply Sn_le_m__n_le_m in H.
      apply H.
  - induction n1.
    * rewrite <- plus_O_n in H. apply H.
    * apply IHn1.
      rewrite -> plus_Sn_m in H.
      apply Sn_le_m__n_le_m in H.
      apply H.
Qed.

Theorem lt_S: forall n m,
    n < m -> n < S m.
Proof.
  unfold lt. intros.
  apply le_S. apply H.
Qed.

Require Export Tactics.

Theorem leb_complete: forall n m,
    leb n m = true -> n <= m.
Proof.
  intros n. induction n.
  intros m H.
  - apply O_le_n.
  - destruct m. intros H.
    inversion H.
    intros H. simpl in H. apply n_le_m__Sn_le_Sm. apply IHn. apply H.
Qed.

 
Theorem leb_correct: forall n m,
    n <= m -> leb n m = true.
Proof.
  intros. generalize dependent n.
  induction m as [|m' IH].
  - intros. inversion H. reflexivity.
  - intros. destruct n as [|n'].
    * reflexivity.
    * simpl. apply IH. apply Sn_le_Sm__n_le_m. apply H.
Qed.

Theorem ev_minus2_: forall n,
    ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  induction E as [|n' E'].
  - simpl. apply ev_0.
  - simpl. apply E'.
Qed.

Theorem evSS_ev_: forall n,
    ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E.
  - apply H0.
Qed.


Lemma ev_even__: forall n,
    ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E.
  - exists 0. reflexivity.
  - destruct IHE as [k H].
    exists (S k).
    rewrite H.
    reflexivity.
Qed.

Theorem leb_true_trans: forall n m o,
    leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o H1 H2.
  apply leb_correct.
  apply leb_complete in H1.
  apply leb_complete in H2.
  apply le_trans with (n:= m).
  apply H1. apply H2.
Qed.

Theorem leb_iff: forall n m,
    leb n m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Module R.
  Inductive R: nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 : forall m n o, R m n o -> R (S m) n (S o)
  | c3 : forall m n o, R m n o -> R m (S n) (S o)
  | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
  | c5 : forall m n o, R m n o -> R n m o.

  Lemma r112: R 1 1 2.
  Proof.
    apply c2.
    apply c3.
    apply c1.
  Qed.

  Lemma r226: R 2 2 6.
  Proof.
  Abort.

  Definition fR: nat -> nat -> nat :=
    fun m n=> m + n .

  Theorem R_euqiv_fR: forall m n o, R m n o <-> fR m n = o.
  Proof.
    intros. split.
    - intros. induction H.
      * reflexivity.
      * admit.
      * admit.
      * admit.
      * admit.
    - intros. induction o.
      * inversion H.
  Admitted.
End R.

Inductive subseq: list nat -> list nat -> Prop :=
| subseq_nil : forall l, subseq [] l
| subseq_beg : forall l1 l2 x, subseq l1 l2 -> subseq (x :: l1) (x :: l2)
| subseq_end : forall l1 l2 x, subseq l1 l2 -> subseq l1 (x :: l2).

Theorem subseq_refl: forall (l: list nat),
    subseq l l.
Proof.
  intros l. induction l.
  - constructor.
  - constructor. apply IHl.
Qed.

Theorem subseq_app: forall (l1 l2 l3: list nat),
    subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H. induction H.
  - constructor.
  - simpl.
    constructor.
    apply IHsubseq.
  - simpl.
    constructor.
    apply IHsubseq.
Qed.

Theorem subseq_cons: forall (x: nat) (l1 l2: list nat),
    subseq (x :: l1) l2 -> subseq [x] l2 /\ subseq l1 l2.
Proof.
  intros. split. induction l2.
  - inversion H.
  - constructor. apply IHl2.
Admitted.


Theorem subseq_trans: forall (l1 l2 l3: list nat),
    subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2. induction H1.
  - constructor.
  - Admitted.

Inductive reg_exp (T: Type) :=
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Inductive exp_match {T: Type} : list T -> reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 e1 s2 e2, exp_match s1 e1 -> exp_match s2 e2 -> exp_match (s1 ++ s2) (App e1 e2)
| MUnionL : forall s e1 e2, exp_match s e1 -> exp_match s (Union e1 e2)
| MUnionR : forall s e1 e2, exp_match s e2 -> exp_match s (Union e1 e2)
| MStar0 : forall e, exp_match [] (Star e)
| MStarApp : forall s1 s2 e, exp_match s1 e -> exp_match s2 (Star e) -> exp_match (s1 ++ s2) (Star e).

Notation "s =~ e" := (exp_match s e)
                       (at level 80).

Example reg_exp_ex1: [1] =~ Char 1.
Proof.
  constructor.
Qed.

Example reg_exp_ex2: [1;2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2] _).
  constructor.
  constructor.
Qed.

Example reg_exp_ex3: ~([1;2] =~ Char 1).
Proof.
  intros H.
  inversion H.
Qed.

Fixpoint reg_exp_of_list {T: Type} (l: list T) :=
  match l with
  | [] => EmptyStr
  | x :: t => App (Char x) (reg_exp_of_list t)
  end.

Example reg_exp_ex4: [1;2;3] =~ reg_exp_of_list [1;2;3].
Proof.
  simpl.
  apply (MApp [1]). constructor.
  apply (MApp [2]). constructor.
  apply (MApp [3]). constructor.
  constructor.
Qed.

Lemma MStar1: forall T s (re : reg_exp T),
    s =~ re -> s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  apply H. constructor.
Qed.

Lemma empty_is_empty: forall T (s: list T),
    ~(s =~ EmptySet).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma MUnion: forall T (s: list T) e1 e2,
    s =~ e1 \/ s =~ e2 -> s =~ Union e1 e2.
Proof.
  intros T s e1 e2 [H | H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.

Lemma MStar': forall T (ss: list (list T)) (re: reg_exp T),
    (forall s, In s ss -> s =~ re) -> fold app ss [] =~ Star re.
Proof.
  intros. induction ss.
  - simpl. constructor.
  - simpl. simpl in H.
    apply MStarApp.
    * apply H. left. reflexivity.
    * apply IHss. intros.
      apply H. right. apply H0.
Qed.
  
Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros. split.
  - generalize dependent s1. induction s2.
    + intros. inversion H. reflexivity.
    + intros. inversion H. inversion H3.
      apply f_equal. apply IHs2.
      apply H4.
  - generalize dependent s1. induction s2.
    + intros. rewrite H. constructor.
    + intros. rewrite H. simpl. apply (MApp [x]).
      * constructor.
      * apply IHs2. reflexivity.
Qed.

Fixpoint re_chars {T} (re: reg_exp T): list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match: forall T (s: list T) (re: reg_exp T) (x: T),
    s =~ re -> In x s -> In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch.
  - apply Hin.
  - apply Hin.
  - simpl. rewrite In_app_inff in *. destruct Hin as [Hin | Hin].
    + left. apply IHHmatch1. apply Hin.
    + right. apply IHHmatch2. apply Hin.
  - simpl. rewrite In_app_inff in *. left. apply IHHmatch. apply Hin.
  - simpl. rewrite In_app_inff in *. right. apply IHHmatch. apply Hin.
  - inversion Hin.
  - simpl. rewrite In_app_inff in *.
    destruct Hin as [Hin | Hin].
    + apply (IHHmatch1 Hin).
    + apply (IHHmatch2 Hin).
Qed.

Fixpoint re_not_empty {T: Type} (re: reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re1 re2  => (re_not_empty re1) && (re_not_empty re2)
  | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
  | Star re => true
  end.

Lemma re_not_empty_correct: forall T (re: reg_exp T),
    (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros. split.
  - intros H. induction re.
    + destruct H. inversion H.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite andb_true_iff. destruct H. inversion H. split.
      * apply IHre1. exists s1. apply H3.
      * apply IHre2. exists s2. apply H4.
    + simpl. rewrite orb_true_iff. destruct H. inversion H.
      * left. apply IHre1. exists x. apply H2.
      * right. apply IHre2. exists x. apply H2.
    + reflexivity.
  - intros H. induction re.
    + inversion H.
    + exists []. constructor.
    + exists [t]. constructor.
    + simpl in H. rewrite andb_true_iff in H.
      destruct H as [H1 H2].
      apply IHre1 in H1. destruct H1 as [s1 H1].
      apply IHre2 in H2. destruct H2 as [s2 H2].
      exists (s1 ++ s2). constructor.
      apply H1. apply H2.
    + simpl in H. rewrite orb_true_iff in H.
      destruct H as [H1 | H2].
      * apply IHre1 in H1. destruct H1 as [s H1].
        exists s. apply MUnionL. apply H1.
      * apply IHre2 in H2. destruct H2 as [s H2].
        exists s. apply MUnionR. apply H2.
    + exists []. apply MStar0.
Qed.

Lemma star_app: forall T (s1 s2: list T) (re: reg_exp T),
    s1 =~ Star re -> s2 =~ Star re -> s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1 H2.
  remember (Star re) as re'.
  generalize dependent s2. induction H1.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - intros. apply H2.
  - inversion Heqre'.
    inversion