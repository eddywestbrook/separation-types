Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Wf.
Require Import Omega.

Require Import SepTypes.OrderedType SepTypes.OFuns SepTypes.PChainEmbed.

Notation "f '∘' g" := (compose_ofun g f) (at level 65) : ofun_scope.
Open Scope ofun_scope.

Arguments clos_trans {_}.
Arguments clos_refl_trans {_}.


(** Functors on ordered types. *)
Section functor.
  Definition TypeF :=
    forall X, OType X -> Type.

  Class OTypeF (F : TypeF) : Type :=
    oTypeF :> forall X oX, OType (F X oX).

  Class FMap (F : TypeF) {oF : OTypeF F} : Type :=
    fmap : forall {X Y oX oY}, (X -o> Y) -> F X oX -o> F Y oY.

  Class ChooseF (F : TypeF) : Type :=
    chooseF : F unit _.

  Class Functor (F : TypeF) {oF : OTypeF F} {fm : FMap F} {ch : ChooseF F}
    : Prop :=
    { fmap_id : forall A oA, fmap (@id_ofun A oA) =o= id_ofun
    ; fmap_comp : forall A B C `{OType A} `{OType B} `{OType C}
                    (f : A -o> B) (g : B -o> C),
        fmap (g ∘ f) =o= fmap g ∘ fmap f
    ; fmap_Proper : forall A B `{OType A} `{OType B},
        Proper (@oeq (A -o> B) _ ==> oeq) fmap }.
End functor.


(** The Embed and proj functions from/to unit can be defined uniformly
    for all functors. *)
Definition unitEmbed {F} `{Functor F} : unit -o> F unit _ :=
  const_ofun chooseF.

Definition unitProj {A} `{OType A} : A -o> unit := const_ofun tt.

Lemma unitEmbed_unitProj_id F `{Functor F} :
  unitProj ∘ unitEmbed =o= id_ofun.
Proof. split; intros [] []; reflexivity. Qed.

Lemma compose_pair_ofun A B C D E F `{OType A} `{OType B} `{OType C}
      `{OType D} `{OType E} `{OType F}
      (f : A -o> C) (g : B -o> D) (h : C -o> E) (k : D -o> F) :
  pair_ofun (h ∘ fst_ofun) (k ∘ snd_ofun) ∘
            pair_ofun (f ∘ fst_ofun) (g ∘ snd_ofun) =o=
  pair_ofun (h ∘ f ∘ fst_ofun) (k ∘ g ∘ snd_ofun).
Proof.
  split; intros [] [] [Hleq1 Hleq2]; rewrite Hleq1, Hleq2; reflexivity.
Qed.


(** Mapping a functor over a diagram. Can also be thought of
    postcomposition of a functor. *)
Section pDiagramMap.
  Definition typeSequenceMap (f : nat -> Type) `{OTypeSequence f}
             F `{Functor F} : nat -> Type :=
    fun n => F (f n) _.

  Global Instance OTypeSequenceMap (f : nat -> Type) `{OTypeSequence f}
         F `{Functor F} : OTypeSequence (typeSequenceMap f F) :=
    fun n => oF (f n) _.

  Global Program Instance PDiagramMap (f : nat -> Type) `{G : PDiagram f}
         F `{func : Functor F}
    : PDiagram (typeSequenceMap f F) :=
    {| embed := fun n => fmap (embed n)
     ; proj := fun n => fmap (proj n) |}.
  Next Obligation.
    destruct func.
    etransitivity.
    symmetry. apply fmap_comp0.
    destruct G.
    simpl. rewrite embed_proj_id. apply fmap_id0.
  Qed.
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

  Fixpoint embed_n (n : nat) : type_n n -o> type_n (S n) :=
    match n with
    | O => unitEmbed
    | S n' => fmap (embed_n n')
    end.

  Fixpoint proj_n (n : nat) : type_n (S n) -o> type_n n :=
    match n with
    | O => unitProj
    | S n' => fmap (proj_n n')
    end.

  Lemma embed_n_proj_n_id n :
    proj_n n ∘ embed_n n =o= id_ofun.
  Proof.
    induction n.
    - apply unitEmbed_unitProj_id.
    - simpl.
      destruct H. rewrite <- fmap_comp0.
      rewrite IHn. apply fmap_id0.
  Qed.

  Global Instance FunctorOTypeSequence
    : OTypeSequence type_n := fun n => _.

  Global Program Instance FunctorPDiagram : PDiagram type_n :=
    {| embed := embed_n
       ; proj := proj_n |}.
  Next Obligation. apply embed_n_proj_n_id. Qed.

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


(** The constant functor for some fixed ordered type T. *)
Section constantFunctor.
  Context T `{OType T} (el : T).
  Definition ConstantF : TypeF := fun _ _ => T.
  Global Instance ConstantOTypeF : OTypeF ConstantF := fun _ _ => _.
  Global Instance ConstantFMap : FMap ConstantF :=
    fun _ _ _ _ _ => id_ofun.
  Global Instance ConstantChooseF : ChooseF ConstantF := el.
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
  Global Instance IdentityChooseF : ChooseF IdentityF := tt.
  Global Program Instance IdentityFunctor : Functor IdentityF.
  Solve Obligations with reflexivity. 
  Global Instance IdentityUnfoldTypeF : UnfoldTypeF IdentityF :=
    fun f _ _ => PChain f.
  Global Instance IdentityUnfoldOTypeF : UnfoldOTypeF IdentityF :=
    fun _ _ _ => _.

  (* :( *)
  (* Global Program Instance IdentityFoldF : FoldF IdentityF := *)
  (*   fun _ _ _ _ _ => id_ofun. *)

  (* This works and is good enough for the identity functor, but a
     similar problem appears in the product functor which is more
     annoying. *)
  (* Global Program Instance IdentityUnfoldF : UnfoldF IdentityF := *)
  (*   fun _ _ _ => {| ofun_app := fun c => {| chain := fun n => chain c n |} |}. *)
  (* Next Obligation. destruct c as [? Hc]; apply Hc. Qed. *)
  (* Next Obligation. firstorder. Qed. *)

  Global Program Instance IdentityFoldF : FoldF IdentityF :=
    fun _ _ _ => {| ofun_app := fun c => {| chain := fun n => chain c n |} |}.
  Next Obligation. destruct c as [? Hc]; apply Hc. Qed.
  Next Obligation. intros ? ? ?; assumption. Qed.

  Global Instance IdentityContinuousFunctor : ContinuousFunctor IdentityF.
  Proof. firstorder. Qed.
  (* constructor. *)
  (*   - intros f o e p G; split; unfold oleq; simpl; *)
  (*       unfold oleq; simpl; firstorder. *)
  (*   - firstorder. *)
  (* Qed. *)
End identityFunctor.


(** The product functor. *)
Section productFunctor.
  Context F1 {oF1 : OTypeF F1} {fm1 : FMap F1} {ch1 : ChooseF F1}
          {func1 : Functor F1} {uF1 : UnfoldTypeF F1}
          {uoF1 : UnfoldOTypeF F1} {foldF1 : FoldF F1}
          {unfoldF1 : UnfoldF F1} {cFunc1 : ContinuousFunctor F1}
          F2 {oF2 : OTypeF F2} {fm2 : FMap F2} {ch2 : ChooseF F2}
          {func2 : Functor F2} {uF2 : UnfoldTypeF F2}
          {uoF2 : UnfoldOTypeF F2} {foldF2 : FoldF F2}
          {unfoldF2 : UnfoldF F2} {cFunc2 : ContinuousFunctor F2}.

  Definition ProductF : TypeF := fun X oX => prod (F1 X oX) (F2 X oX).

  Global Instance ProductOTypeF : OTypeF ProductF := fun _ _ => OTpair _ _ _ _.

  Global Program Instance ProductFMap : FMap ProductF :=
    fun _ _ _ _ => fun f => pair_ofun (fmap f ∘ fst_ofun)
                                (fmap f ∘ snd_ofun).

  Global Instance ProductEmbedF : ChooseF ProductF :=
    (chooseF, chooseF).

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
    - intros A B oA oB f g Heq.
      unfold fmap, ProductFMap.
      destruct func1, func2.
      rewrite Heq. reflexivity.
  Qed.

  Global Instance ProductUnfoldTypeF : UnfoldTypeF ProductF :=
  fun f _ _ => prod (@unfoldTypeF F1 uF1 f _ _)
                 (@unfoldTypeF F2 uF2 f _ _).
  Global Instance ProductUnfoldOTypeF :
    UnfoldOTypeF ProductF := fun _ _ _ => _.

  Global Program Instance ProductUnfoldF : UnfoldF ProductF :=
    fun f _ _ =>
      (* pair_ofun (unfoldF f ∘ fst_ofun) (unfoldF f ∘ snd_ofun) ∘ unzipPChain. *)
      {| ofun_app :=
           fun x =>
             (pair_ofun (unfoldF f ∘ fst_ofun) (unfoldF f ∘ snd_ofun) ∘ unzipPChain) @@ x |}.
  Global Program Instance ProductFoldF : FoldF ProductF :=
    fun f _ _ =>
      zipPChain ∘ pair_ofun (foldF f ∘ fst_ofun) (foldF f ∘ snd_ofun).


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

  (* Lemma compose_pair_ofun A B C D E F `{OType A} `{OType B} `{OType C}
        `{OType D} `{OType E} `{OType F}
        (f : A -o> C) (g : B -o> D) (h : C -o> E) (k : D -o> F) :
    pair_ofun (h ∘ fst_ofun) (k ∘ snd_ofun) ∘
              pair_ofun (f ∘ fst_ofun) (g ∘ snd_ofun) =o=
    pair_ofun (h ∘ f ∘ fst_ofun) (k ∘ g ∘ snd_ofun).
  Proof.
    split; intros [] [] [Hleq1 Hleq2];rewrite Hleq1, Hleq2; reflexivity.
  Qed. *)

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


(* This is the basic core of fmap for both the preorder and PER
   functors. *)
Definition fmapRel {A B} `{OType A} `{OType B} (f : A -o> B)
           (R : relation A) : relation B :=
  fun y1 y2 => exists x1 x2, f @@ x1 =o= y1 /\ f @@ x2 =o= y2 /\ R x1 x2.


(* The class of proper preorders. *)
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
    clos_refl_trans (fmapRel (fmap f) (proj1_sig R)).
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

  Global Program Instance PreOrderChooseF : ChooseF PreOrderF :=
    fun _ _ => True.
  Next Obligation. firstorder. Qed.

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


(* The class of partial equivalence relations (PERs). *)
Class PER {A} `{OType A} (R : relation A) : Prop :=
  { Proper_PER :> Proper (oeq ==> oeq ==> oleq) R
  ; Symmetric_PER :> Symmetric R
  ; Transitive_PER :> Transitive R }.

(** The PER functor. *)
Section perFunctor.
  Definition PERF : TypeF := fun X oX => {R : relation X | PER R}.

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
    clos_trans (fmapRel (fmap f) (proj1_sig R)).
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

  Global Program Instance PERChooseF : ChooseF PERF :=
    fun _ _ => True.
  Next Obligation. firstorder. Qed.

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


(** A simple inductive type for binary trees with an order relation
    and an fmap operation. *)
Section tree.
  Inductive Tree A :=
  | Leaf : A -> Tree A
  | Node : Tree A -> Tree A -> Tree A.

  Global Arguments Leaf {_}.
  Global Arguments Node {_}.

  Inductive tree_oleq {A} `{OType A} : Tree A -> Tree A -> Prop :=
  | tree_oleq_Leaf : forall x y,
      x <o= y ->
      tree_oleq (Leaf x) (Leaf y)
  | tree_oleq_Node : forall t1 t2 t1' t2',
      tree_oleq t1 t1' ->
      tree_oleq t2 t2' ->
      tree_oleq (Node t1 t2) (Node t1' t2').

  Global Instance Reflexive_tree_oleq {A} `{OType A} : Reflexive tree_oleq.
  Proof. intro x; induction x; constructor; auto; reflexivity. Qed.

  Global Instance Transitive_tree_oleq {A} `{OType A} : Transitive tree_oleq.
  Proof.
    intros x y z Hxy Hyz; revert x z Hxy Hyz.
    induction y; intros; destruct x, z;
      inversion Hxy; inversion Hyz; subst.
    - constructor; etransitivity; eauto.
    - constructor.
      + apply IHy1; auto.
      + apply IHy2; auto.
  Qed.

  Global Program Instance OTtree A `(OType A) : OType (Tree A) :=
    {| oleq := tree_oleq |}.
  Next Obligation.
    constructor.
    - apply Reflexive_tree_oleq.
    - apply Transitive_tree_oleq.
  Qed.

  Inductive isLeaf {A} : Tree A -> Prop :=
  | isLeafLeaf : forall x, isLeaf (Leaf x).

  Inductive isNode {A} : Tree A -> Prop :=
  | isNodeNode : forall t1 t2, isNode (Node t1 t2).

  Definition isLeafb {A} (t : Tree A) : bool :=
    match t with
    | Leaf _ => true
    | Node _ _ => false
    end.

  Definition isNodeb {A} (t : Tree A) : bool :=
    match t with
    | Leaf _ => false
    | Node _ _ => true
    end.

  Lemma isLeaf_isLeafb A (t : Tree A) :
    isLeaf t <-> isLeafb t = true.
  Proof.
    split; intros H; inversion H; auto; destruct t.
    - constructor.
    - simpl in H; congruence.
  Qed.

  Lemma isNode_isNodeb A (t : Tree A) :
    isNode t <-> isNodeb t = true.
  Proof.
    split; intros H; inversion H; auto; destruct t.
    - simpl in H; congruence.
    - constructor.
  Qed.

  (* tree_oleq is reflexive wrt equivalence. *)
  Lemma Reflexive'_tree_oleq A `{OType A} t1 t2 :
    t1 =o= t2 ->
    tree_oleq t1 t2.
  Proof. firstorder. Qed.

  Global Instance Proper_tree_oleq' A `{OType A} :
    Proper (oeq ==> oeq ==> oleq) tree_oleq.
  Proof.
    intros x y Hleq1 z w Hleq2 Hleq3.
    rewrite <- Hleq1.
    etransitivity; eauto.
    apply Reflexive'_tree_oleq; auto.
  Qed.

  Global Instance Proper_Leaf {A} `{OType A} :
    Proper (oleq ==> oleq) Leaf.
  Proof. constructor; auto. Qed.

  Global Instance Proper_Node {A} `{OType A} :
    Proper (oleq ==> oleq ==> oleq) Node.
  Proof. constructor; auto. Qed.

  (* Plain-old fmap for trees. *)
  Fixpoint tree_fmap {A B} `{OType A} `{OType B} (f : A -o> B)
           (t : Tree A) : Tree B :=
    match t with
    | Leaf x => Leaf (f @@ x)
    | Node t1 t2 => Node (tree_fmap f t1) (tree_fmap f t2)
    end.

  Global Instance Proper_tree_fmap {A B} `{OType A} `{OType B} (f : A -o> B) :
    Proper (oleq ==> oleq) (tree_fmap f).
  Proof.
    intros x y Hleq; induction Hleq; simpl.
    + rewrite H1; reflexivity.
    + constructor; auto.
  Qed.

  (* OFun version of fmap. *)
  Program Definition Tree_fmap {A B} `{OType A} `{OType B} (f : A -o> B)
    : Tree A -o> Tree B :=
    {| ofun_app := fun t => tree_fmap f t |}.
  Next Obligation.
    intros t1 t2 Hleq; induction Hleq; simpl.
    - rewrite H1; reflexivity.
    - constructor; auto.
  Qed.

  Global Instance Proper_Tree_fmap {A B} `{OType A} `{OType B} :
    Proper (@oleq (A -o> B) _ ==> oleq) (Tree_fmap).
  Proof.
    intros ? ? ? ? ? Hleq2; induction Hleq2; constructor; auto.
  Qed.

  Global Instance Proper_Tree_fmap' {A B} `{OType A} `{OType B} :
    Proper (@oeq (A -o> B) _ ==> oeq) (Tree_fmap).
  Proof. intros ? ? Heq; split; apply Proper_Tree_fmap; apply Heq. Qed.

  (* tree_fmap satisfies the functor laws. *)
  Lemma tree_fmap_id A `{OType A} x :
    tree_fmap id_ofun x =o= x.
  Proof.
    induction x.
    - reflexivity.
    - simpl; rewrite IHx1, IHx2; reflexivity.
  Qed.

  Lemma Tree_fmap_id A `{OType A} :
    Tree_fmap id_ofun =o= id_ofun.
  Proof.
    generalize (tree_fmap_id A); intros H0; split;
      intros t1 t2 Hleq; simpl; rewrite H0; auto.
  Qed.

  Lemma Tree_fmap_comp A B C `{OType A} `{OType B} `{OType C}
        (f : A -o> B) (g : B -o> C) :
    Tree_fmap (g ∘ f) =o= Tree_fmap g ∘ Tree_fmap f.
  Proof.
    split; intros t1 t2 Hleq; unfold oleq; simpl;
      induction Hleq; constructor; auto; rewrite H2; reflexivity.
  Qed.

  (* Get the element out of a leaf. If the argument isn't a leaf, just
     recurse to the left until one is found. *)
  Fixpoint unLeaf {A} (t : Tree A) : A :=
    match t with
    | Leaf x => x
    | Node t1 _ => unLeaf t1 (* shouldn't happen *)
    end.

  Global Instance Proper_unLeaf {A} `{OType A} :
    Proper (oleq ==> oleq) unLeaf.
  Proof. intros ? ? Heq; induction Heq; auto. Qed.

  Lemma leaf_unleaf A (t : Tree A) :
    isLeaf t ->
    Leaf (unLeaf t) = t.
  Proof. intros Hleaf; inversion Hleaf; auto. Qed.

  (* OFun version of unLeaf *)
  Definition unLeaf' {A} `{OType A} : Tree A -o> A :=
    {| ofun_app := unLeaf; ofun_Proper := Proper_unLeaf |}.

  (* Get the left subtree of a tree. If the argument is a leaf, just
     return it unchanged. *)
  Fixpoint unNodeLeft {A} (t : Tree A) : Tree A :=
    match t with
    | Leaf _ => t (* shouldn't happen *)
    | Node t1 _ => t1
    end.

  Global Instance Proper_unNodeLeft {A} `{OType A} :
    Proper (oleq ==> oleq) unNodeLeft.
  Proof.
    intros ? ? Heq; induction Heq; auto; simpl; rewrite H0; reflexivity.
  Qed.

  (* OFun version of unNodeLeft *)
  Definition unNodeLeft' {A} `{OType A} : Tree A -o> Tree A :=
    {| ofun_app := unNodeLeft; ofun_Proper := Proper_unNodeLeft |}.

  (* Get the right subtree of a tree. If the argument is a leaf, just
     return it unchanged. *)
  Fixpoint unNodeRight {A} (t : Tree A) : Tree A :=
    match t with
    | Leaf _ => t (* shouldn't happen *)
    | Node _ t2 => t2
    end.

  Global Instance Proper_unNodeRight {A} `{OType A} :
    Proper (oleq ==> oleq) unNodeRight.
  Proof.
    intros ? ? Heq; induction Heq; auto; simpl; rewrite H0; reflexivity.
  Qed.

  (* OFun version of unNodeRight *)
  Definition unNodeRight' {A} `{OType A} : Tree A -o> Tree A :=
    {| ofun_app := unNodeRight; ofun_Proper := Proper_unNodeRight |}.
End tree.


(** Map the Tree type constructor and fmap over a diagram. *)
Section mapTreePDiagram.
  Definition mapTreeTypeSequence f `{PDiagram f} : nat -> Type :=
    fun n => Tree (f n).
  Global Instance MapTreeOTypeSequence f `{PDiagram f}
    : OTypeSequence (mapTreeTypeSequence f) := fun n => _.
  Global Instance MapTreePDiagram f `{PDiagram f}
    : PDiagram (mapTreeTypeSequence f) := fun n => Tree_fmap (proj n).
End mapTreePDiagram.


(** Operations and proofs related to chains of trees. *)
Section treePChain.
  Program Definition unLeafPChain {f} `{PDiagram f}
  : PChain (mapTreeTypeSequence f) -o> PChain f :=
    pChainMap (mapTreeTypeSequence f) f
              (fun _ => {| ofun_app := fun x => unLeaf' @@ x |}) _.
  Next Obligation.
    unfold oeq, oleq; split; simpl; intros ? ? Heq;
      induction Heq; simpl; auto; rewrite H0; reflexivity.
  Qed.

  Program Definition unNodeLeftPChain {f} `{PDiagram f}
    : PChain (mapTreeTypeSequence f) -o> PChain (mapTreeTypeSequence f) :=
    pChainMap (mapTreeTypeSequence f) (mapTreeTypeSequence f)
              (fun _ => {| ofun_app := fun x => unNodeLeft' @@ x |}) _.
  Next Obligation.
    split; simpl; intros c1 c2 Hleq; induction Hleq;
      try apply Proper_tree_fmap; auto; constructor;
        rewrite H0; reflexivity.
  Qed.

  Program Definition unNodeRightPChain {f} `{PDiagram f}
    : PChain (mapTreeTypeSequence f) -o> PChain (mapTreeTypeSequence f) :=
    pChainMap (mapTreeTypeSequence f) (mapTreeTypeSequence f)
              (fun _ => {| ofun_app := fun x => unNodeRight' @@ x |}) _.
  Next Obligation.
    split; simpl; intros c1 c2 Hleq; induction Hleq;
      try apply Proper_tree_fmap; auto; constructor;
        rewrite H0; reflexivity.
  Qed.

  Lemma unNodeLeftPChain_oleq {f} `{PDiagram f} (c1 c2 : PChain (mapTreeTypeSequence f)) :
    c1 <o= c2 ->
    unNodeLeftPChain @@ c1 <o= unNodeLeftPChain @@ c2.
  Proof.
    intros Hleq n; simpl; specialize (Hleq n);
      destruct (chain c1 n), (chain c2 n);
      inversion Hleq; subst; auto.
  Qed.

  Lemma unNodeRightPChain_oleq {f} `{PDiagram f} (c1 c2 : PChain (mapTreeTypeSequence f)) :
    c1 <o= c2 ->
    unNodeRightPChain @@ c1 <o= unNodeRightPChain @@ c2.
  Proof.
    intros Hleq n; simpl; specialize (Hleq n);
      destruct (chain c1 n), (chain c2 n);
      inversion Hleq; subst; auto.
  Qed.

  Program Definition treeFold {f} `{PDiagram f} :
    Tree (PChain f) -o> PChain (mapTreeTypeSequence f) :=
    {| ofun_app :=
         fun t =>
           {| chain := fun n => Tree_fmap (chainProj n) @@ t |} |}.
  Next Obligation.
    induction t; simpl.
    - destruct a; apply (Proper_oeq_oleq_op1 _ _ _ Proper_Leaf);
        apply chainCondition0.
    - apply (Proper_oeq_oleq_op2 _ _ _ _ Proper_Node); auto.
  Qed.
  Next Obligation.
    intros x y Heq n. simpl.
    induction Heq; simpl in *.
    - specialize (H0 n). apply Proper_Leaf; auto.
    - apply Proper_Node; auto.
  Qed.

  Fixpoint treeUnfold_f_aux {f} `{PDiagram f}
           (c : PChain (mapTreeTypeSequence f))
           (t : Tree (f 0))
    : Tree (PChain f) :=
    match t with
    | Leaf _ => Leaf (unLeafPChain @@ c)
    | Node t1 t2 => Node (treeUnfold_f_aux (unNodeLeftPChain @@ c) t1)
                        (treeUnfold_f_aux (unNodeRightPChain @@ c) t2)
    end.

  Global Instance Proper_treeUnfold_f_aux f `{PDiagram f} :
    Proper (oeq ==> oeq ==> oeq) treeUnfold_f_aux.
  Proof.
    intros c1 c2 Heq1 x y Heq2.
    split; unfold oleq; simpl.
    - destruct Heq2 as [Heq2 _].
      revert c1 c2 Heq1.
      induction Heq2; intros.
      + constructor; intros n; destruct Heq1; simpl;
          rewrite (H1 n); reflexivity.
      + constructor.
        * apply IHHeq2_1; destruct Heq1 as [Heq1 Heq2]; split;
            unfold oleq; simpl; intros n; try rewrite (Heq1 n);
              try rewrite (Heq2 n); reflexivity.
        * apply IHHeq2_2; destruct Heq1 as [Heq1 Heq2]; split;
            unfold oleq; simpl; intros n; try rewrite (Heq1 n);
              try rewrite (Heq2 n); reflexivity.
    - destruct Heq2 as [_ Heq2].
      revert c1 c2 Heq1.
      induction Heq2; intros.
      + constructor; intros n; destruct Heq1; simpl;
          rewrite (H2 n); reflexivity.
      + constructor.
        * apply IHHeq2_1; destruct Heq1 as [Heq1 Heq2]; split;
            unfold oleq; simpl; intros n; try rewrite (Heq1 n);
              try rewrite (Heq2 n); reflexivity.
        * apply IHHeq2_2; destruct Heq1 as [Heq1 Heq2]; split;
            unfold oleq; simpl; intros n; try rewrite (Heq1 n);
              try rewrite (Heq2 n); reflexivity.
  Qed.

  Definition treeUnfold_f {f} `{PDiagram f}
           (c : PChain (mapTreeTypeSequence f))
    : Tree (PChain f) :=
    treeUnfold_f_aux c (chain c 0).

  Global Instance Proper_treeUnfold_f {f} `{PDiagram f} :
    Proper (oleq ==> oleq) treeUnfold_f.
  Proof.
    intros c1 c2 Hleq.
    unfold oleq in *. simpl in *.
    unfold treeUnfold_f.
    pose proof Hleq as Hleq'.
    specialize (Hleq' 0).
    remember (chain c1 0) as x.
    remember (chain c2 0) as y.
    revert Heqx Heqy. revert c1 c2 Hleq.
    induction Hleq'; intros.
    - simpl. constructor. intros ?. simpl.
      rewrite Hleq. reflexivity.
    - simpl. constructor.
      + assert (H0: t1 = chain (unNodeLeftPChain @@ c1) 0).
        { simpl; destruct (chain c1 0); inversion Heqx; auto. }
        assert (H1: t1' = chain (unNodeLeftPChain @@ c2) 0).
        { simpl; destruct (chain c2 0); inversion Heqy; auto. }
        specialize (IHHleq'1 (unNodeLeftPChain @@ c1)
                             (unNodeLeftPChain @@ c2)
                             (unNodeLeftPChain_oleq _ _ Hleq) H0 H1).
        etransitivity. apply IHHleq'1.
        apply Reflexive'_tree_oleq. reflexivity.
      + assert (H0: t2 = chain (unNodeRightPChain @@ c1) 0).
        { simpl; destruct (chain c1 0); inversion Heqx; auto. }
        assert (H1: t2' = chain (unNodeRightPChain @@ c2) 0).
        { simpl; destruct (chain c2 0); inversion Heqy; auto. }
        specialize (IHHleq'2 (unNodeRightPChain @@ c1)
                             (unNodeRightPChain @@ c2)
                             (unNodeRightPChain_oleq _ _ Hleq) H0 H1).
        etransitivity. apply IHHleq'2.
        apply Reflexive'_tree_oleq. reflexivity.
  Qed.

  Definition treeUnfold {f} `{PDiagram f}
    : PChain (mapTreeTypeSequence f) -o> Tree (PChain f) :=
    {| ofun_app := treeUnfold_f |}.

  Lemma isLeaf_oleq A `{OType A} (t1 t2 : Tree A) :
    isLeaf t1 -> t1 <o= t2 -> isLeaf t2.
  Proof.
    intros Hleaf Hleq; inversion Hleq; subst;
      try constructor; inversion Hleaf.
  Qed.

  Lemma isNode_oleq A `{OType A} (t1 t2 : Tree A) :
    isNode t1 -> t1 <o= t2 -> isNode t2.
  Proof.
    intros Hnode Hleq; inversion Hleq; subst;
      try constructor; inversion Hnode.
  Qed.

  Lemma isLeaf_fmap {A B} `{OType A} `{OType B} (t : Tree A) (f : A -o> B) :
    isLeaf (tree_fmap f t) -> isLeaf t.
  Proof.
    intros Hleaf; destruct t. constructor. inversion Hleaf.
  Qed.

  Lemma isNode_fmap {A B} `{OType A} `{OType B} (t : Tree A) (f : A -o> B) :
    isNode (tree_fmap f t) -> isNode t.
  Proof.
    intros Hnode. destruct t. inversion Hnode. constructor.
  Qed.

  Lemma isLeaf_chain f `{PDiagram f} (c : PChain (mapTreeTypeSequence f)) n :
    isLeaf (chain c 0) -> isLeaf (chain c n).
  Proof.
    intros Hleaf; inversion Hleaf.
    destruct c; simpl in *.
    induction n.
    - rewrite <- H1; constructor.
    - specialize (chainCondition0 n).
      generalize (isLeaf_oleq _ (chain0 n)
                              (tree_fmap (proj n) (chain0 (S n)))
                              IHn (proj1 chainCondition0)); intros Hleaf'.
      apply isLeaf_fmap in Hleaf'; auto.
  Qed.

  Lemma isNode_chain f `{PDiagram f} (c : PChain (mapTreeTypeSequence f)) n :
    isNode (chain c 0) -> isNode (chain c n).
  Proof.
    intros Hnode; inversion Hnode.
    destruct c; simpl in *.
    induction n.
    - rewrite <- H1; constructor.
    - specialize (chainCondition0 n).
      generalize (isNode_oleq _ (chain0 n)
                              (tree_fmap (proj n) (chain0 (S n)))
                              IHn (proj1 chainCondition0)); intros Hnode'.
      apply isNode_fmap in Hnode'; auto.
  Qed.

  Lemma tree_fold_unfold f `{PDiagram f} :
    treeFold ∘ treeUnfold =o= id_ofun.
  Proof.
    split; simpl.
    - intros c1 c2 Hleq n. unfold oleq; simpl.
      unfold treeUnfold_f.
      transitivity (chain c1 n).
      + clear Hleq c2; remember (chain c1 0); revert c1 Heqm.
        induction m; intros; simpl.
        * assert (isLeaf (chain c1 n)).
          { apply isLeaf_chain; rewrite <- Heqm; constructor. }
          rewrite leaf_unleaf; auto; reflexivity.
        * assert (isNode (chain c1 n)).
          { apply isNode_chain; rewrite <- Heqm; constructor. }
          inversion H0; subst; constructor.
          -- assert (H1: m1 = chain (unNodeLeftPChain @@ c1) 0).
             { simpl; destruct (chain c1 0); inversion Heqm; auto. }
             specialize (IHm1 (unNodeLeftPChain @@ c1) H1).
             etransitivity. apply IHm1.
             simpl; rewrite <- H2; reflexivity.
          -- assert (H1: m2 = chain (unNodeRightPChain @@ c1) 0).
            { simpl; destruct (chain c1 0); inversion Heqm; auto. }
            specialize (IHm2 (unNodeRightPChain @@ c1) H1).
            etransitivity. apply IHm2.
            simpl; rewrite <- H2; reflexivity.
      + apply Hleq.
    - intros c1 c2 Hleq n. unfold oleq; simpl.
      transitivity (chain c2 n).
      + apply Hleq.
      + clear Hleq c1; unfold treeUnfold_f; remember (chain c2 0).
        revert c2 Heqm; induction m; intros; simpl.
        * assert (isLeaf (chain c2 n)).
          { apply isLeaf_chain; rewrite <- Heqm; constructor. }
          rewrite leaf_unleaf; auto; reflexivity.
        * assert (isNode (chain c2 n)).
          { apply isNode_chain; rewrite <- Heqm; constructor. }
          inversion H0; subst; constructor.
          -- assert (H1: m1 = chain (unNodeLeftPChain @@ c2) 0).
             { simpl; destruct (chain c2 0); inversion Heqm; auto. }
             specialize (IHm1 (unNodeLeftPChain @@ c2) H1).
             transitivity (chain (unNodeLeftPChain @@ c2) n).
             { simpl. rewrite <- H2. simpl. reflexivity. }
             etransitivity; eauto. reflexivity.
          -- assert (H1: m2 = chain (unNodeRightPChain @@ c2) 0).
             { simpl; destruct (chain c2 0); inversion Heqm; auto. }
             specialize (IHm2 (unNodeRightPChain @@ c2) H1).
             transitivity (chain (unNodeRightPChain @@ c2) n).
             { simpl. rewrite <- H2. simpl. reflexivity. }
             etransitivity; eauto. reflexivity.
  Qed.

  Lemma tree_unfold_fold f `{PDiagram f} :
    treeUnfold ∘ treeFold =o= id_ofun.
  Proof.
    split; unfold oleq; simpl.
    - intros t1 t2 Hleq. unfold oleq; simpl.
      induction Hleq; simpl in *.
      + constructor; auto.
      + unfold treeUnfold_f in *. simpl in *.
        constructor.
        * match goal with
          | [ _ : tree_oleq ?x t1' |- _ ] => transitivity x
          end; auto;
          apply Reflexive'_tree_oleq;
          apply Proper_treeUnfold_f_aux;
          split; simpl; unfold oleq; simpl; reflexivity;
          reflexivity.
        * match goal with
          | [ _ : tree_oleq ?x t2' |- _ ] => transitivity x
          end; auto.
          apply Reflexive'_tree_oleq.
          apply Proper_treeUnfold_f_aux.
          split; simpl; unfold oleq; simpl; reflexivity.
          reflexivity.
    - intros t1 t2 Hleq.
      induction Hleq; simpl in *.
      + transitivity (Leaf y). constructor; auto.
        apply Reflexive'_tree_oleq.
        split; constructor; unfold oleq; simpl; reflexivity.
      + constructor; etransitivity; try apply IHHleq1;
          try apply IHHleq2; apply Reflexive'_tree_oleq;
            unfold treeUnfold_f; simpl; apply Proper_treeUnfold_f_aux;
              split; unfold oleq; simpl; reflexivity.
  Qed.
End treePChain.

(** The tree functor. *)
Section treeFunctor.
  Context F {oF : OTypeF F} {fm : FMap F} {ch : ChooseF F}
          {func : Functor F} {uF : UnfoldTypeF F} {uOF : UnfoldOTypeF F}
          {fF : FoldF F} {ufF : UnfoldF F} {cFunc : ContinuousFunctor F}.

  Definition TreeF : TypeF := fun X oX => Tree (F X oX).

  Global Instance TreeOTypeF : OTypeF TreeF := fun _ _ => _.

  Global Instance TreeFMap : FMap TreeF :=
    fun _ _ _ _ => fun f => Tree_fmap (fmap f).

  Global Instance TreeChooseF : ChooseF TreeF := Leaf chooseF.

  Global Program Instance TreeFunctor : Functor TreeF.
  Next Obligation.
    unfold fmap, TreeFMap; destruct func.
    rewrite fmap_id0; apply Tree_fmap_id.
  Qed.
  Next Obligation.
    unfold fmap, TreeFMap; destruct func.
    rewrite fmap_comp0; apply Tree_fmap_comp.
  Qed.

  Global Instance TreeUnfoldTypeF : UnfoldTypeF TreeF :=
  fun f _ _ => Tree (@unfoldTypeF F uF f _ _).
  Global Instance TreeUnfoldOTypeF : UnfoldOTypeF TreeF := fun _ _ _ => _.
  Global Instance TreeFoldF : FoldF TreeF :=
    fun f _ _ => treeFold ∘ Tree_fmap (foldF f).
  Global Instance TreeUnfoldF : UnfoldF TreeF :=
    fun f _ _ => Tree_fmap (unfoldF f) ∘ treeUnfold.
  Global Instance TreeContinuousFunctor : ContinuousFunctor TreeF.
  Proof.
    constructor.
    - intros f o G.
      unfold unfoldF, TreeUnfoldF, foldF, TreeFoldF.
      rewrite compose_ofun_assoc_4.
      rewrite tree_unfold_fold.
      rewrite id_compose_ofun.
      match goal with
      | [ |- Tree_fmap ?f ∘ Tree_fmap ?g =o= _ ] =>
        transitivity (Tree_fmap (f ∘ g))
      end.
      symmetry.
      apply Tree_fmap_comp.
      destruct cFunc. rewrite unfold_fold_id0.
      apply Tree_fmap_id.
    - intros f o G.
      unfold unfoldF, TreeUnfoldF, foldF, TreeFoldF.
      rewrite compose_ofun_assoc_4.
      rewrite compose_ofun_middle_id.
      apply tree_fold_unfold.
      match goal with
      | [ |- Tree_fmap ?f ∘ Tree_fmap ?g =o= _ ] =>
        transitivity (Tree_fmap (f ∘ g))
      end.
      symmetry; apply Tree_fmap_comp.
      destruct cFunc. rewrite fold_unfold_id0.
      apply Tree_fmap_id.
  Qed.
End treeFunctor.


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

Notation "'ϕ'" := unfoldCompose (at level 65) : mem_scope.
Notation "'ψ'" := foldCompose (at level 65) : mem_scope.
Notation "a '×' b" := (ProductF a b) (at level 65) : mem_scope.
Notation "'|' x '|'" := (ConstantF x) (at level 65) : mem_scope.
Notation "'ϒ' x" := (TreeF x) (at level 65) : mem_scope.

Open Scope mem_scope.

(** The recursive type for memory stores. *)
Section mem.
  Context Z `{OType Z}.

  Definition permF : TypeF := PERF × PreOrderF.

  Definition memF : TypeF := |Z| × ϒ permF.

  Definition MemDiag : nat -> Type := type_n memF.
  Definition Mem := PChain (type_n memF).

  Definition MemPERDiag f `{PDiagram f} := typeSequenceMap f PERF.
  Definition MemPER f `{PDiagram f} := PChain (MemPERDiag f).

  Definition MemPreOrderDiag f `{PDiagram f} := typeSequenceMap f PreOrderF.
  Definition MemPreOrder f `{PDiagram f} := PChain (MemPreOrderDiag f).

  Definition Perm f `{PDiagram f} := (MemPER f * MemPreOrder f)%type.

  (* These are a bit slow to typecheck... *)
  (* But at least they verify that the UnfoldF instance generated by
     typeclass resolution is the type we expect. *)
  (* Definition unfoldSanityCheck : Mem -o> Z * Tree Perm := ϕ memF. *)
  (* Definition foldSanityCheck : Z * Tree Perm -o> Mem := ψ memF. *)

  Definition memPEREq {f} `{PDiagram f} (per : MemPER f)
    : relation (PChain f) :=
    fun c1 c2 => forall n, proj1_sig (chain per n) (chain c1 n) (chain c2 n).

  Definition memPreOrderEq {f} `{PDiagram f} (po : MemPreOrder f)
    : relation (PChain f) :=
    fun c1 c2 => forall n, proj1_sig (chain po n) (chain c1 n) (chain c2 n).

  Definition permEq {f} `{PDiagram f} (p : Perm f) : relation (PChain f) :=
    memPEREq (fst p).

  Definition permUpd {f} `{PDiagram f} (p : Perm f) : relation (PChain f) :=
    memPreOrderEq (snd p).

  (* Definition R_true A : relation A := fun _ _ => True. *)
  (* Definition PER_true A `{OType A} : PER (R_true A). *)
  (* Proof. firstorder. Qed. *)

  (* Definition contramap_rel {f} `{PDiagram f} {n} (R : relation (f n))
    : relation (f (S n)) := *)
  (*   fun x y => R (proj n @@ x) (proj n @@ y). *)

  (* Fixpoint test_f (n0 n1 : nat) n : nat := *)
  (*   match n with *)
  (*   | O => n0 *)
  (*   | 1 => n1 *)
  (*   | S n' => 1 + test_f n0 n1 n' *)
  (*   end. *)

  (* Program Fixpoint mkPER1_f {f} `{PDiagram f} n *)
  (*         (R1 : relation (f 1)) {struct n} : relation (f n) := *)
  (*   match n with *)
  (*   | O => fun _ _ => True *)
  (*   | S O => R1 *)
  (*   | S n0 => contramap_rel (mkPER1_f n0 R1) *)
  (*   (* | S n' => fun x y => mkPER1_f n' R0 R1 (proj n' @@ x) (proj n' @@ y) *) *)
  (*   end. *)

  (* Program Fixpoint mkPER1_f {f} `{PDiagram f} *)
  (*         (R1 : relation (f 1)) n : relation (f n) := *)
  (*   match n with *)
  (*   | O => fun _ _ => True *)
  (*   | S n' => match n' with *)
  (*            | O => R1 *)
  (*            | _ => _ (contramap_rel (mkPER1_f R1 n')) *)
  (*            end *)
  (*   end. *)

  Definition contramap_rel {A B} `{OType A} `{OType B} (f : A -o> B)
             (R : relation B) : relation A :=
    fun x y => R (f @@ x) (f @@ y).

  Definition coerce_rel {f} `{PDiagram f} {n m}
             (R : relation (f n)) (pf : n = m) : relation (f m) :=
    match pf with
    | eq_refl => R
    end.

  Program Fixpoint mkPER1_f {f} `{PDiagram f}
          (R1 : relation (f 1)) n {struct n} : relation (f n) :=
    match n with
    | O => fun _ _ => True
    | S n' => match n' with
             | O => R1
             | S n'' => contramap_rel (proj (S n''))
                                     (coerce_rel (mkPER1_f R1 n') _)
             end
    end.

  Program Fixpoint mkPreOrder1_f {f} `{PDiagram f}
          (R1 : relation (f 1)) n {struct n} : relation (f n) :=
    match n with
    | O => fun _ _ => True
    | S n' => match n' with
             | O => R1
             | S n'' => contramap_rel (proj (S n''))
                                     (coerce_rel (mkPreOrder1_f R1 n') _)
             end
    end.

  Program Definition mkPER1 {f} `{PDiagram f} (R : relation (f 1)) {per : PER R}
    : MemPER f :=
    {| chain := mkPER1_f R |}.
  Next Obligation.
    rename x into n.
    constructor.
    - intros x y Heq1 z w Heq2 Hr.
      induction n; auto.
      simpl in *. destruct n.
      + destruct per. rewrite <- Heq1, <- Heq2; auto.
      + eapply IHn; eauto. rewrite Heq1; reflexivity.
        rewrite Heq2; reflexivity.
    - intros x y Hr.
      induction n; auto.
      simpl. destruct n.
      + simpl in *. destruct per; auto.
      + simpl in *.
        apply IHn. auto.
    - intros x y z Hzy Hyz.
      induction n; auto.
      simpl. destruct n. simpl in *.
      destruct per; eapply Transitive_PER0; eauto.
      eapply IHn; eauto.
  Qed.

  Next Obligation.
    split.
    - intros x y Hr. simpl in *.
      induction n.
      apply t_step.
      unfold fmapRel.
      exists chooseF.
      admit.
      simpl in Hr. destruct n; simpl in *.
      + specialize (IHn (proj 0 @@ x) (proj 0 @@ y) I).
        inversion IHn; subst.
        * destruct H1 as (x1 & x2 & ? & ? & ?).
          
  Admitted.

  Program Definition mkPreOrder1 {f} `{PDiagram f} (R : relation (f 1))
          {po : Preorder R} : MemPreOrder f :=
    {| chain := mkPreOrder1_f R |}.
  Next Obligation.
    rename x into n.
    constructor.
    - intros x y Heq1 z w Heq2 Hr.
      induction n; auto.
      simpl in *. destruct n.
      + destruct po. rewrite <- Heq1, <- Heq2; auto.
      + eapply IHn; eauto. rewrite Heq1; reflexivity.
        rewrite Heq2; reflexivity.
    - constructor.
      + intros x. induction n; simpl; auto.
        destruct n. destruct po as [_ []]; auto.
        apply IHn.
      + intros x y z Hxy Hyz. induction n; auto.
        destruct n; simpl.
        destruct po as [_ []].
        eapply PreOrder_Transitive; eauto.
        eapply IHn; eauto.
  Qed.

  Next Obligation. Admitted.

End mem.
