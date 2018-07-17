Require Export SepTypes.OrderedType.


(***
 *** Downward Closed Sets
 ***)

Record DownSet A `{OType A} : Type :=
  { inDownSet : A -> Prop;
    downSetClosed :
      forall a1 a2, oleq a2 a1 -> inDownSet a1 -> inDownSet a2 }.

Arguments inDownSet {A _} _ _.
Arguments downSetClosed {A _} _.

Instance OType_DownSet A `{OType A} : OType (DownSet A) :=
  {| oleq ds1 ds2 := (inDownSet ds1) <o= (inDownSet ds2) |}.
Proof.
  constructor.
  - intro. reflexivity.
  - intros ds1 ds2 ds3; transitivity (inDownSet ds2); assumption.
Defined.

Instance Proper_inDownSet A `{OType A} :
  Proper (oleq ==> oleq --> oleq) (inDownSet (A:=A)).
Proof.
  repeat intro.
  apply H0. eapply downSetClosed; eassumption.
Qed.

Program Definition emptyDownSet {A} `{OType A} : DownSet A :=
  {| inDownSet a := False |}.

Program Definition completeDownSet {A} `{OType A} : DownSet A :=
  {| inDownSet a := True |}.

Program Definition downClose {A} `{OType A} (a:A) : DownSet A :=
  {| inDownSet a' := a' <o= a |}.
Next Obligation.
  etransitivity; eassumption.
Defined.

Instance Proper_downClose A `{OType A} :
  Proper (oleq ==> oleq) (downClose (A:=A)).
Proof.
  intros a1 a2 R12 a'; simpl; intro in_a'. etransitivity; eassumption.
Qed.

Program Definition unionDownSet {A} `{OType A} (ds1 ds2: DownSet A) : DownSet A :=
  {| inDownSet := fun a => inDownSet ds1 a \/ inDownSet ds1 a;
     downSetClosed := _ |}.
Next Obligation.
  destruct H1; [ left | right ]; eapply downSetClosed; eassumption.
Defined.

Program Definition bindDownSet {A B} `{OType A} `{OType B}
           (dsA: DownSet A) (f: A -> DownSet B) : DownSet B :=
  {| inDownSet := fun b => exists a, inDownSet dsA a /\ inDownSet (f a) b;
     downSetClosed := _ |}.
Next Obligation.
  exists H2; split; try assumption.
  apply (downSetClosed _ _ _ H1 H4).
Defined.

Instance Proper_bindDownSet A B `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) (bindDownSet (A:=A) (B:=B)).
Proof.
  intros ds1 ds2 Rds f1 f2 Rf b; simpl; intro in_b.
  destruct in_b as [ a [in_ds1 in_f1]].
  exists a; split.
  - apply Rds; assumption.
  - apply Rf; assumption.
Qed.

Instance Proper_bindDownSet_equiv A B `{OType A} `{OType B} :
  Proper (oeq ==> oeq ==> oeq) (bindDownSet (A:=A) (B:=B)).
Proof.
  intros ds1 ds2 Rds f1 f2 Rf; destruct Rds; destruct Rf.
  split; apply Proper_bindDownSet; assumption.
Qed.

Definition mapDownSet {A B} `{OType A} `{OType B} (f:A -> B) dsA : DownSet B :=
  bindDownSet dsA (fun a => downClose (f a)).


(***
 *** Monad laws for DownSet
 ***)

Lemma DownSet_return_bind {A B} `{OType A} `{OType B} a (f : A -> DownSet B) :
  Proper (oleq ==> oleq) f ->
  bindDownSet (downClose a) f =o= f a.
Proof.
  intros. simpl. split; simpl; repeat intro.
  - destruct H2. destruct H2. rewrite H2 in H3. assumption.
  - exists a; split; simpl; [ reflexivity | assumption ].
Qed.

Lemma DownSet_bind_return {A B} `{OType A} `{OType B} (ds: DownSet A) :
  bindDownSet ds downClose =o= ds.
Proof.
  split; simpl; repeat intro.
  - destruct H1. destruct H1. rewrite H2. assumption.
  - exists a; split; simpl; [ assumption | reflexivity ].
Qed.

Lemma DownSet_assoc {A B C} `{OType A} `{OType B} `{OType C}
      ds (f: A -> DownSet B) (g: B -> DownSet C) :
  bindDownSet (bindDownSet ds f) g =o=
  bindDownSet ds (fun x => bindDownSet (f x) g).
Proof.
  split; simpl; intro c; repeat intro.
  - destruct H2 as [ b [ [ a [ in_a in_b ]] in_c]].
    exists a; split; [ assumption | ].
    exists b; split; assumption.
  - destruct H2 as [ a [ in_a [ b [ in_b in_c ]]]].
    exists b; split; [ | assumption ].
    exists a; split; assumption.
Qed.


(***
 *** DownSets and Fixed-points
 ***)

(* We define the fixed-point of a set function transformer f as the intersection
of all f-closed functions g *)
Program Definition fixDownSet {A B} `{OType B}
        (f: (A -> DownSet B) -> (A -> DownSet B)) (a:A) : DownSet B :=
  {| inDownSet b :=
       forall g, f g <o= g -> inDownSet (g a) b
  |}.
Next Obligation.
  apply (downSetClosed _ _ _ H0). apply H1. apply H2.
Defined.

(* NOTE: what we really want is Proper-ness of (fixDownSet f), i.e.,
w.r.t. the A argument, which only holds for functions f that are Proper
w.r.t. (oleq ==> oleq ==> oleq) *)
(*
Instance Proper_fixDownSet {A B} `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (fixDownSet (A:=A) (B:=B)).
Proof.
  admit.
Admitted.
*)

(* We then prove this is a fixed-point using the Knaster-Tarski theorem *)
Lemma fixDownSetUnfold {A B} `{OType B}
      (f: (A -> DownSet B) -> A -> DownSet B)
      (prp: Proper (oleq ==> oleq) f) :
  (fixDownSet (A:=A) (B:=B) f) =o= f (fixDownSet f).
Proof.
  assert (f (fixDownSet f) <o= fixDownSet f).
  - intros a b in_b g g_f_closed.
    assert (f (fixDownSet f) <o= g).
    + etransitivity; try eassumption. apply prp.
      intros a' b' in_b'. apply in_b'. assumption.
    + apply H0; assumption.
  - split; [ | apply H0 ].
    simpl; repeat intro. apply (H1 _ (prp _ _ H0)).
Qed.


(***
 *** DownSets as Graphs of Proper Functions
 ***)

(* A function graph for a Proper function f is a set of (in, out) pairs
satisfying out <o= f in. The graph is thus closed under out getting smaller and
in getting bigger. *)
Definition FunGraph A B `{OType A} `{OType B} := DownSet (Flip A * B).

Definition lambdaDownSet {A B} `{OType A} `{OType B}
           (f: A -> DownSet B) : FunGraph A B :=
  bindDownSet completeDownSet
              (fun a => mapDownSet (fun b => (flip a,b)) (f a)).

Instance Proper_lambdaDownSet {A B} `{OType A} `{OType B} :
  Proper (oleq ==> oleq) (lambdaDownSet (A:=A) (B:=B)).
Proof.
  intros f1 f2 Rf. unfold lambdaDownSet.
  apply Proper_bindDownSet; try reflexivity.
  intro a. apply Proper_bindDownSet; [ apply Rf; assumption | ].
  intro b. reflexivity.
Qed.

Program Definition applyDownSet {A B} `{OType A} `{OType B}
        (f: FunGraph A B) (a : A) : DownSet B :=
  {| inDownSet := fun b => inDownSet f (flip a,b) |}.
Next Obligation.
  rewrite H1. assumption.
Defined.

Instance Proper_applyDownSet {A B} `{OType A} `{OType B} :
  Proper (oleq ==> oleq ==> oleq) applyDownSet.
Proof.
  intros f1 f2 Rf a1 a2 Ra b. simpl. rewrite Rf. rewrite Ra. reflexivity.
Qed.

Instance Proper_applyDownSet_equiv {A B} `{OType A} `{OType B} :
  Proper (oeq ==> oeq ==> oeq) applyDownSet.
Proof.
  intros f1 f2 Rf a1 a2 Ra; destruct Rf; destruct Ra.
  split; apply Proper_applyDownSet; assumption.
Qed.


(* lambdaDownSet can make the outputs for a function bigger if it is not Proper,
because (in1, out) being in the graph implies that (in2, out) for any in1 <o=
in2, even if (f in2) is incomparable to out *)
Lemma downSetBeta_leq {A B} `{OType A} `{OType B} (f: A -> DownSet B) :
  f <o= applyDownSet (lambdaDownSet f).
Proof.
  intros a b in_b. simpl.
  exists a; split; [ trivial | ].
  exists b; split; [ assumption | reflexivity ].
Qed.

(* If a function is Proper, however, then equality holds *)
Lemma downSetBeta {A B} `{OType A} `{OType B} (f: A -> DownSet B) :
  Proper (oleq ==> oleq) f -> f =o= applyDownSet (lambdaDownSet f).
Proof.
  intros prp. split; [ apply downSetBeta_leq | ].
  intros a b [ a' [ _ [ b' [ in_b' [ Ra Rb ] ]]]].
  unfold oleq, OTFlip in Ra. simpl in Ra, Rb.
  rewrite Rb. rewrite <- Ra. assumption.
Qed.

Lemma downSetEta {A B} `{OType A} `{OType B} (f: FunGraph A B) :
  lambdaDownSet (applyDownSet f) =o= f.
Proof.
  split.
  { intros [ a b ] [ a' [ _ [ b' [ in_b' [ Ra Rb ] ]]]]. simpl in Ra, Rb.
    rewrite Ra. rewrite Rb. assumption. }
  { intros [[ a ] b ] in_ab. simpl.
    exists a; split; [ trivial | ].
    exists b; split; [ assumption | reflexivity ]. }
Qed.
