Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Wf.
Require Import Omega.

Require Import SepTypes.OrderedType SepTypes.OFuns SepTypes.PChain.

Open Scope ofun_scope.

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.


(** A generic proj function for all functors. *)
Definition unitProj {A} `{OType A} : A -o> unit := const_ofun tt.


(** Functors on ordered types. *)
Section functor.
  Definition TypeF :=
    forall X, OType X -> Type.

  Class OTypeF (F : TypeF) : Type :=
    oTypeF :> forall X oX, OType (F X oX).

  Class FMap (F : TypeF) {oF : OTypeF F} : Type :=
    fmap : forall {X Y oX oY}, (X -o> Y) -> F X oX -o> F Y oY.

  Class Functor (F : TypeF) {oF : OTypeF F} {fm : FMap F}
    : Prop :=
    { fmap_id : forall A oA, fmap (@id_ofun A oA) =o= id_ofun
    ; fmap_comp : forall A B C `{OType A} `{OType B} `{OType C}
                    (f : A -o> B) (g : B -o> C),
        fmap (g ∘ f) =o= fmap g ∘ fmap f }.
End functor.


(** Mapping a functor over a diagram. Can also be thought of
    postcomposition of a functor. *)
Section pDiagramMap.
  Definition typeSequenceMap (f : nat -> Type) `{PDiagram f}
             F `{func : Functor F} : nat -> Type :=
    fun n => F (f n) _.
  Global Instance OTypeSequenceMap (f : nat -> Type) `{PDiagram f}
         F `{func : Functor F}
    : OTypeSequence (typeSequenceMap f F) :=
    fun n => oF (f n) _.

  Global Program Instance PDiagramMap (f : nat -> Type) `{G : PDiagram f}
         F `{func : Functor F}
    : PDiagram (typeSequenceMap f F) :=
    fun n => fmap (proj n).
End pDiagramMap.


(** A continuous functor provides fold and unfold morphisms and a
    proof that they are an isomorphism. The type that they unfold to
    is specified by the functor, so it isn't guaranteed to be
    meaningful. E.g., the preorder and PER functors just use the
    identity morphism for fold and unfold, and the proof of
    isomorphism is trivial. *)
Section continuousFunctor.
  Class UnfoldTypeF (F : TypeF) : Type :=
    unfoldTypeF : forall f `{PDiagram f}, Type.

  Class UnfoldOTypeF F {U : UnfoldTypeF F} : Type :=
    unfoldOTypeF :> forall f `{PDiagram f}, OType (unfoldTypeF f).

  Class UnfoldF F `{Functor F} {U : UnfoldTypeF F} {UO : UnfoldOTypeF F}
    : Type :=
    unfoldF : forall f `{PDiagram f},
      PChain (typeSequenceMap f F) -o> unfoldTypeF f.

  Class FoldF F `{Functor F} {U : UnfoldTypeF F} {UO : UnfoldOTypeF F}
    : Type :=
    foldF : forall f `{PDiagram f},
      unfoldTypeF f -o> PChain (typeSequenceMap f F).

  Class ContinuousFunctor F `{Functor F} {U : UnfoldTypeF F}
        {UO : UnfoldOTypeF F} {fold : FoldF F} {unfold : UnfoldF F}
    : Prop :=
    { unfold_fold_id : forall f `{PDiagram f},
        unfoldF f ∘ foldF f =o= id_ofun
    ; fold_unfold_id : forall f `{PDiagram f},
        foldF f ∘ unfoldF f =o= id_ofun }.  
End continuousFunctor.


(** Construct a diagram by iterated application of a functor. *)
Section functorPDiagram.
  Context F `{Functor F}.

  Record TypeWithInstances : Type :=
    { TWI_ty :> Type
    ; TWI_OType :> OType TWI_ty
    }.

  Global Instance OType_TypeWithInstances twi : OType (TWI_ty twi) :=
    TWI_OType twi.
  Typeclasses Transparent OType_TypeWithInstances.

  Fixpoint type_n (n : nat) : TypeWithInstances :=
    match n with
    | O => {| TWI_ty := unit |}
    | S n' =>
      let t := type_n n' in
      {| TWI_ty := F (TWI_ty t) _ |}
    end.

  Fixpoint proj_n (n : nat) : type_n (S n) -o> type_n n :=
    match n with
    | O => unitProj
    | S n' => fmap (proj_n n')
    end.

  Global Instance FunctorOTypeSequence
    : OTypeSequence type_n := fun n => _.
  Global Instance FunctorPDiagram : PDiagram type_n := proj_n.

  Program Definition functorUnfold
    : PChain type_n -o> PChain (typeSequenceMap type_n F) :=
    {| ofun_app := fun f => {| chain := fun n => chain f (S n) |} |}.
  Next Obligation.
    destruct f as [c Hc]; simpl; specialize (Hc (S n)); auto.
  Qed.
  Next Obligation.
    intros c1 c2 Hleq n; specialize (Hleq (S n)); auto.
  Qed.

  Program Definition functorFold
    : PChain (typeSequenceMap type_n F) -o> PChain type_n :=
    {| ofun_app :=
         fun f =>
           {| chain := fun n => match n with
                             | O => tt
                             | S n' => chain f  n'
                             end |} |}.
  Next Obligation.
    destruct n. reflexivity. destruct f as [c Hc]; apply Hc.
  Qed.
  Next Obligation.
    intros c1 c2 Hleq n; destruct n. reflexivity. apply Hleq.
  Qed.

  Lemma functor_unfold_fold :
    functorUnfold ∘ functorFold =o= id_ofun.
  Proof. split; intros c1 c2 Hleq; apply Hleq. Qed.

  Lemma functor_fold_unfold :
    functorFold ∘ functorUnfold =o= id_ofun.
  Proof.
    split; intros c1 c2 Hleq []; simpl;
      destruct (chain c1 0), (chain c2 0);
      try reflexivity; apply (Hleq (S n)).
  Qed.
End functorPDiagram.


(* A couple convenience lemmas. *)
Lemma compose_ofun_assoc_4 A B C D E `{OType A} `{OType B} `{OType C} `{OType D}
      `{OType E} (f : A -o> B) (g : B -o> C) (h : C -o> D) (k : D -o> E) :
  (k ∘ h) ∘ (g ∘ f) =o= k ∘ (h ∘ g) ∘ f.
Proof. split; intros ? ? Hleq; rewrite Hleq; reflexivity. Qed.

Lemma compose_ofun_middle_id A B C `{OType A} `{OType B} `{OType C} (f : A -o> B)
      (g : B -o> C) (h : C -o> B) (k : B -o> A) :
  h ∘ g =o= id_ofun ->
  k ∘ (h ∘ g) ∘ f =o= k ∘ f.
Proof.
  intros Hid; rewrite Hid; rewrite id_compose_ofun; reflexivity.
Qed.

Lemma compose_pair_ofun A B C D E F `{OType A} `{OType B} `{OType C}
      `{OType D} `{OType E} `{OType F}
      (f : A -o> C) (g : B -o> D) (h : C -o> E) (k : D -o> F) :
  pair_ofun (h ∘ fst_ofun) (k ∘ snd_ofun) ∘
            pair_ofun (f ∘ fst_ofun) (g ∘ snd_ofun) =o=
  pair_ofun (h ∘ f ∘ fst_ofun) (k ∘ g ∘ snd_ofun).
Proof.
  split; intros [] [] [Hleq1 Hleq2];rewrite Hleq1, Hleq2; reflexivity.
Qed.


Section foldUnfoldComposition.
  Context F `{ContinuousFunctor F}.

  Definition unfoldCompose : PChain (type_n F) -o> unfoldTypeF (type_n F) :=
    unfoldF (type_n F) ∘ functorUnfold F.

  Definition foldCompose : unfoldTypeF (type_n F) -o> PChain (type_n F) :=
    functorFold F ∘ foldF (type_n F).

  Lemma unfoldCompose_foldCompose :
    unfoldCompose ∘ foldCompose =o= id_ofun.
  Proof.
    unfold unfoldCompose, foldCompose.
    rewrite compose_ofun_assoc_4.
    rewrite functor_unfold_fold.
    rewrite id_compose_ofun.
    destruct H0. auto.
  Qed.

  Lemma foldCompose_unfoldCompose :
    foldCompose ∘ unfoldCompose =o= id_ofun.
  Proof.
    unfold unfoldCompose, foldCompose.
    rewrite compose_ofun_assoc_4.
    destruct H0. auto.
    rewrite fold_unfold_id0.
    rewrite id_compose_ofun.
    apply functor_fold_unfold.
  Qed.
End foldUnfoldComposition.


(** The constant functor for some fixed ordered type T. *)
Section constantFunctor.
  Context T `{OType T}.
  Definition ConstantF : TypeF := fun _ _ => T.
  Global Instance ConstantOTypeF : OTypeF ConstantF := fun _ _ => _.
  Global Instance ConstantFMap : FMap ConstantF :=
    fun _ _ _ _ _ => id_ofun.
  Global Program Instance ConstantFunctor : Functor ConstantF.
  Solve Obligations with firstorder.
  Global Instance ConstantUnfoldTypeF : UnfoldTypeF ConstantF :=
    fun _ _ _ => T.
  Global Instance ConstantUnfoldOTypeF
    : UnfoldOTypeF ConstantF := fun _ _ _ => _.
  Global Program Instance ConstantUnfoldF : UnfoldF ConstantF :=
    fun _ _ _ => {| ofun_app := fun f => chain f 0 |}.
  Next Obligation. firstorder. Qed.
  Global Program Instance ConstantFoldF : FoldF ConstantF :=
    fun _ _ _ => {| ofun_app := fun x => {| chain := fun n => x |} |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. firstorder. Qed.
  Global Instance ConstantContinuousFunctor : ContinuousFunctor ConstantF.
  Proof.
    constructor; intros f o G.
    - split; firstorder.
    - split; simpl; intros x y Heq n.
      + induction n.
        * apply Heq.
        * destruct y as [y Hy]; simpl in *; rewrite <- Hy; auto.
      + induction n.
        * apply Heq.
        * destruct x as [x Hx]; simpl in *; rewrite <- Hx; auto.
  Qed.
End constantFunctor.


(** The identity functor. *)
Section identityFunctor.
  Definition IdentityF : TypeF := fun X _ => X.
  Global Instance IdentityOTypeF : OTypeF IdentityF := fun _ oX => oX.
  Global Instance IdentityFMap : FMap IdentityF :=
    fun _ _ _ _ => id.
  Global Program Instance IdentityFunctor : Functor IdentityF.
  Solve Obligations with reflexivity.
  Global Instance IdentityUnfoldTypeF : UnfoldTypeF IdentityF :=
    fun f _ _ => PChain f.
  Global Instance IdentityUnfoldOTypeF : UnfoldOTypeF IdentityF :=
    fun _ _ _ => _.
  Global Program Instance IdentityUnfoldF : UnfoldF IdentityF :=
    fun _ _ _ => id_ofun.
  Global Program Instance IdentityFoldF : FoldF IdentityF :=
    fun _ _ _ => id_ofun.
  Global Instance IdentityContinuousFunctor : ContinuousFunctor IdentityF.
  Proof. firstorder. Qed.
End identityFunctor.


(** The product functor. *)
Section productFunctor.
  Context F1 {oF1 : OTypeF F1} {fm1 : FMap F1} {func1 : Functor F1}
          {uF1 : UnfoldTypeF F1} {uoF1 : UnfoldOTypeF F1}
          {foldF1 : FoldF F1} {unfoldF1 : UnfoldF F1}
          {cFunc1 : ContinuousFunctor F1}
          F2 {oF2 : OTypeF F2} {fm2 : FMap F2} {func2 : Functor F2}
          {uF2 : UnfoldTypeF F2} {uoF2 : UnfoldOTypeF F2}
          {foldF2 : FoldF F2} {unfoldF2 : UnfoldF F2}
          {cFunc2 : ContinuousFunctor F2}.

  Definition ProductF : TypeF := fun X oX => prod (F1 X oX) (F2 X oX).

  Global Instance ProductOTypeF : OTypeF ProductF := fun _ _ => OTpair _ _ _ _.

  Global Program Instance ProductFMap : FMap ProductF :=
    fun _ _ _ _ => fun f => pair_ofun (fmap f ∘ fst_ofun)
                                (fmap f ∘ snd_ofun).

  Global Instance ProductFunctor : Functor ProductF.
  Proof.
    constructor.
    - intros A oA.
      split; simpl.
      + intros [] [] []; split; simpl; try rewrite H; try rewrite H0;
          destruct func1, func2; try rewrite fmap_id0;
            try rewrite fmap_id1; reflexivity.
      + split; destruct func1, func2; simpl; try rewrite fmap_id0;
          try rewrite fmap_id1; apply H.
    - intros A B C oA oB oC f g.
      split; split; simpl; destruct func1, func2;
        solve [rewrite fmap_comp0, H; reflexivity |
               rewrite fmap_comp1, H; reflexivity].
  Qed.

  Global Instance ProductUnfoldTypeF : UnfoldTypeF ProductF :=
  fun f _ _ => prod (@unfoldTypeF F1 uF1 f _ _) (@unfoldTypeF F2 uF2 f _ _).
  Global Instance ProductUnfoldOTypeF :
    UnfoldOTypeF ProductF := fun _ _ _ => _.

  Global Program Instance ProductUnfoldF : UnfoldF ProductF :=
    fun f _ _ =>
      pair_ofun (unfoldF f ∘ fst_ofun) (unfoldF f ∘ snd_ofun) ∘ unzipPChain.
  Global Program Instance ProductFoldF : FoldF ProductF :=
    fun f _ _ =>
      zipPChain ∘ pair_ofun (foldF f ∘ fst_ofun) (foldF f ∘ snd_ofun).

  Global Instance ProductContinuousFunctor : ContinuousFunctor ProductF.
  Proof.
    constructor; intros f o G.
    - unfold unfoldF, ProductUnfoldF, foldF, ProductFoldF.
      rewrite compose_ofun_assoc_4, unzip_zip_PChain, id_compose_ofun.
      etransitivity. apply compose_pair_ofun.
      destruct cFunc1 as [Huf1 _], cFunc2 as [Huf2 _]; rewrite Huf1;
        rewrite Huf2; rewrite 2!compose_id_ofun; apply pair_fst_snd_eta.
    - unfold unfoldF, ProductUnfoldF, foldF, ProductFoldF.
      rewrite compose_ofun_assoc_4, compose_ofun_middle_id.
      + (* Why won't zip_unzip_PChain apply here? *)
        split; intros c1 c2 Hleq n; apply Hleq.
      + etransitivity. apply compose_pair_ofun.
        destruct cFunc1 as [_ Hfu1], cFunc2 as [_ Hfu2]; rewrite Hfu1;
          rewrite Hfu2; rewrite 2!compose_id_ofun; apply pair_fst_snd_eta.
  Qed.
End productFunctor.


(* This is the core of fmap for both the preorder and PER functors. *)
Definition fmapRel {A B} `{OType A} `{OType B} (f : A -o> B)
           (R : relation A) : relation B :=
  fun y1 y2 => exists x1 x2, f @@ x1 =o= y1 /\ f @@ x2 =o= y2 /\ R x1 x2.


(* The class of proper preorders. Call it Preorder to avoid conflict
   with the regular PreOrder class. *)
Class Preorder {A} `{OType A} (R : relation A) : Prop :=
  { Proper_Preorder :> Proper (oeq ==> oeq ==> oleq) R
  ; PreOrder_Preorder :> PreOrder R }.


Inductive clos_refl_trans {A} `{OType A} (R : relation A) (x : A) : A -> Prop :=
    | rt_step y : R x y -> clos_refl_trans R x y
    | rt_refl y : x =o= y -> clos_refl_trans R x y
    | rt_trans y z :
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

(** The preorder functor. *)
Section preorderFunctor.
  Definition PreOrderF : TypeF := fun X oX => {R : relation X | Preorder R}.

  Global Instance PreOrderOTypeF : OTypeF PreOrderF := fun _ _ => _.

  Global Instance Proper_clos_refl_trans {A} `{OType A} (R : relation A) :
    Proper (oeq ==> oeq ==> oleq) R ->
    Proper (oeq ==> oeq ==> oleq) (clos_refl_trans R).
  Proof.
    intros Hprop x y Heq1 z w Heq2 Hclos.
    revert y w Heq1 Heq2.
    induction Hclos; intros.
    - apply rt_step; rewrite <- Heq1, <- Heq2; auto.
    - apply rt_refl. rewrite <- Heq1. rewrite H0; auto.
    - apply rt_trans with y. apply IHHclos1; auto; reflexivity.
      apply IHHclos2; auto; reflexivity.
  Qed.

  Global Instance Proper_fmapRel {A B} `{OType A} `{OType B}
           (f : A -o> B) (R : relation A) :
    Proper (oeq ==> oeq ==> oleq) R ->
    Proper (oeq ==> oeq ==> oleq) (fmapRel f R). 
  Proof.
    intros Hprop ? ? Heq1 ? ? Heq2 (x1 & x2 & ? & ? & ?).
    exists x1, x2; split.
    - rewrite <- Heq1; auto.
    - split; auto; rewrite <- Heq2; auto.
  Qed.

  Program Definition fmapPreOrder {A B} `{OType A} `{OType B} (f : A -o> B)
          (R : PreOrderF A _) : PreOrderF B _ :=
    clos_refl_trans (fmapRel f (proj1_sig R)).
  Next Obligation.
    constructor.
    - apply Proper_clos_refl_trans, Proper_fmapRel;
        destruct R as [R HR]; destruct HR; auto.
    - constructor.
      + intros ?; apply rt_refl; reflexivity.
      + intros ?; apply rt_trans.
  Qed.

  Global Program Instance PreOrderFMap : FMap PreOrderF :=
    fun _ _ _ _ => fun f => {| ofun_app := fun r => fmapPreOrder f r |}.
  Next Obligation.
    intros R1 R2 Heq1 x y Heq2.
    simpl in *.
    revert R2 Heq1.
    induction Heq2; intros.
    - apply rt_step.
      destruct H3 as (x1 & x2 & ? & ? & ?).
      exists x1, x2. split; auto. split; auto.
      apply Heq1; auto. (* TODO: factor out? *)
    - apply rt_refl; auto.
    - eapply rt_trans; eauto.
  Qed.

  Global Program Instance PreOrderFunctor : Functor PreOrderF.
  Next Obligation.
    split.
    - intros R1 R2 Hleq x y Hclos.
      induction Hclos.
      + destruct H as (x1 & x2 & ? & ? & ?). simpl.
        apply Hleq; destruct R1; rewrite <- H, <- H0; auto.
      + apply Hleq; destruct R1 as [R HR]; rewrite H; apply HR.
      + destruct R2; etransitivity; eauto.
    - intros R1 R2 Hleq1 x y Hleq2.
      apply rt_step; exists x, y; split.
      reflexivity. split. reflexivity. apply Hleq1; auto.
  Qed.
  Next Obligation.
    split.
    - intros R1 R2 Hleq x y Hclos; simpl in *.
      revert R2 Hleq.
      induction Hclos; intros.
      + destruct H2 as (x1 & x2 & ? & ? & ?).
        apply rt_step. exists (fmap f @@ x1), (fmap f @@ x2).
        split; simpl; auto. split; auto.
        apply rt_step; exists x1, x2. split. reflexivity.
        split. reflexivity. apply Hleq; auto.
      + apply rt_refl; auto.
      + eapply rt_trans; eauto.
    - intros R1 R2 Hleq1 x y Hclos; simpl in *.
      revert R2 Hleq1; induction Hclos; intros.
      + destruct H2 as (x1 & x2 & H2 & H3 & Hclos).
        revert x y H2 H3.
        induction Hclos; intros.
        * destruct H2 as (x1 & x2 & H2 & H5 & H6).
          rewrite <- H2 in H3; rewrite <- H5 in H4.
          apply rt_step; exists x1, x2.
          split; auto. split; auto. apply Hleq1; auto.
        * rewrite H2 in H3; rewrite H3 in H4; apply rt_refl; auto.
        * eapply rt_trans. apply IHHclos1; auto. reflexivity.
          apply IHHclos2; auto. reflexivity.
      + apply rt_refl; auto.
      + eapply rt_trans; eauto.
  Qed.

  Global Instance PreOrderUnfoldTypeF : UnfoldTypeF PreOrderF :=
    fun f _ _ => PChain (typeSequenceMap f PreOrderF).
  Global Instance PreOrderUnfoldOTypeF :
    UnfoldOTypeF PreOrderF := fun _ _ _ => _.
  Global Instance PreOrderUnfoldF : UnfoldF PreOrderF := fun _ _ _ => id_ofun.
  Global Instance PreOrderFoldF : FoldF PreOrderF := fun _ _ _ => id_ofun.
  Global Instance PreOrderContinuousFunctor : ContinuousFunctor PreOrderF.
  Proof. constructor; intros; apply id_compose_ofun. Qed.
End preorderFunctor.


(* The class of partial equivalence relations (PERs). Call it Per to
   avoid conflict with the regular PER class. *)
Class Per {A} `{OType A} (R : relation A) : Prop :=
  { Proper_Per :> Proper (oeq ==> oeq ==> oleq) R
  ; Symmetric_Per :> Symmetric R
  ; Transitive_Per :> Transitive R }.

(** The PER functor. *)
Section perFunctor.
  Definition PERF : TypeF := fun X oX => {R : relation X | Per R}.

  Global Instance PEROTypeF : OTypeF PERF := fun _ _ => _.

  Global Instance Proper_clos_trans {A} `{OType A} {R : relation A} :
    Proper (oeq ==> oeq ==> oleq) R ->
    Proper (oeq ==> oeq ==> oleq) (clos_trans R).
  Proof.
    intros Hprop x y Heq1 z w Heq2 Hclos.
    revert y w Heq1 Heq2.
    induction Hclos; intros.
    - apply t_step. rewrite <- Heq1. rewrite <- Heq2. auto.
    - apply t_trans with y. apply IHHclos1; auto; reflexivity.
      apply IHHclos2; auto; reflexivity.
  Qed.

  Instance Symmetric_clos_trans A (R : relation A) :
    Symmetric R ->
    Symmetric (clos_trans R).
  Proof.
    intros Hsym x y Hclos; induction Hclos.
    - apply t_step. apply Hsym; auto.
    - eapply t_trans; eauto.
  Qed.

  Instance Symmetric_fmapRel A B `{OType A} `{OType B} (f : A -o> B) (R : relation A) :
    Symmetric R ->
    Symmetric (fmapRel f R).
  Proof.
    intros Hsym x y (x1 & x2 & ? & ? & ?).
    exists x2, x1. split; auto.
  Qed.

  Program Definition fmapPER {A B} `{OType A} `{OType B} (f : A -o> B)
          (R : PERF A _) : PERF B _ :=
    clos_trans (fmapRel f (proj1_sig R)).
  Next Obligation.
    constructor.
    - apply Proper_clos_trans. apply Proper_fmapRel.
      destruct R; auto. simpl. destruct p; auto.
    - apply Symmetric_clos_trans.
      apply Symmetric_fmapRel.
      destruct R, p; auto.
    - intros ?; eapply t_trans; eauto.
  Qed.

  Global Program Instance PERFMap : FMap PERF :=
    fun _ _ _ _ => fun f => {| ofun_app := fun r => fmapPER f r |}.
  Next Obligation.
    intros R1 R2 Hleq1 x y Hclos. simpl in *.
    induction Hclos.
    - apply t_step.
      destruct H3 as (x1 & x2 & ? & ? & ?).
      exists x1, x2. split; auto. split; auto.
      apply Hleq1; auto.
    - eapply t_trans; eauto.
  Qed.

  (* This is mostly a copy of the preorder functor proof. There's
     probably a way to factor out the common parts but it's much
     easier to just do this. *)
  Global Program Instance PERFunctor : Functor PERF.
  Next Obligation.
    split.
    - intros R1 R2 Hleq x y Hclos.
      induction Hclos.
      + destruct H as (x1 & x2 & ? & ? & ?).
        apply Hleq; destruct R1; rewrite <- H, <- H0; auto.
      + destruct R2; etransitivity; eauto.
    - intros R1 R2 Hleq1 x y Hleq2.
      apply t_step; exists x, y; split.
      reflexivity. split. reflexivity.
      apply Hleq1; auto.
  Qed.
  Next Obligation.
    split.
    - intros R1 R2 Hleq x y Hclos; simpl in *.
      revert R2 Hleq.
      induction Hclos; intros.
      + destruct H2 as (x1 & x2 & ? & ? & ?).
        apply t_step. exists (fmap f @@ x1), (fmap f @@ x2).
        split;  auto.
        split; auto. apply t_step.
        exists x1, x2. split. reflexivity.
        split. reflexivity. apply Hleq; auto.
      + eapply t_trans; eauto.
    - intros R1 R2 Hleq1 x y Hclos; simpl in *.
      revert R2 Hleq1; induction Hclos; intros.
      + destruct H2 as (x1 & x2 & H2 & H3 & Hclos).
        revert x y H2 H3.
        induction Hclos; intros.
        * destruct H2 as (x1 & x2 & H2 & H5 & H6).
          rewrite <- H2 in H3; rewrite <- H5 in H4.
          apply t_step; exists x1, x2.
          split; auto. split; auto. apply Hleq1; auto.
        * eapply t_trans. apply IHHclos1; auto. reflexivity.
          apply IHHclos2; auto. reflexivity.
      + eapply t_trans; eauto.
  Qed.

  Global Instance PERUnfoldTypeF : UnfoldTypeF PERF :=
    fun f _ _ => PChain (typeSequenceMap f PERF).
  Global Instance PERUnfoldOTypeF : UnfoldOTypeF PERF := fun _ _ _ => _.
  Global Program Instance PERUnfoldF : UnfoldF PERF := fun _ _ _ => id_ofun.
  Global Program Instance PERFoldF : FoldF PERF := fun _ _ _ => id_ofun.
  Global Instance PERContinuousFunctor : ContinuousFunctor PERF.
  Proof. constructor; intros; apply id_compose_ofun. Qed.
End perFunctor.
