(* Require Import Coq.Classes.Morphisms. *)
Require Import Coq.Classes.RelationClasses.
(* Require Import Coq.Relations.Relation_Definitions. *)
(* Require Import Coq.Relations.Relation_Operators. *)

Require Import Coq.Program.Wf.
Require Import Omega.

Require Import SepTypes.OrderedType SepTypes.OFuns.

Notation "f '∘' g" := (compose_ofun g f) (at level 65) : ofun_scope.
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
    fmap : forall {X Y oX oY}, (X -o> Y) -o> F X oX -o> F Y oY.

  Class Functor (F : TypeF) {oF : OTypeF F} {fm : FMap F}
    : Prop :=
    { fmap_id : forall A oA, fmap @@ @id_ofun A oA =o= id_ofun
    ; fmap_comp : forall A B C `{OType A} `{OType B} `{OType C}
                    (f : A -o> B) (g : B -o> C),
        fmap @@ (g ∘ f) =o= fmap @@ g ∘ fmap @@ f }.
End functor.


(** Diagrams in the category of ordered types. *)
Section pDiagram.
  Class OTypeSequence (f : nat -> Type) : Type :=
    oTypeSeq :> forall n, OType (f n).
  Class PDiagram (f : nat -> Type) {o : OTypeSequence f} : Type :=
    proj : forall n, f (S n) -o> f n.

  (** "Projective limit" chains. *)
  Record PChain f `{PDiagram f} : Type :=
    { chain : forall n, f n
    ; chainCondition : forall n, chain n =o= proj n @@ (chain (S n)) }.
End pDiagram.

Arguments chain {_ _ _}.

Instance OTPChain f `{PDiagram f} : OType (PChain f) :=
  {| oleq := fun s1 s2 => forall n, chain s1 n <o= chain s2 n |}.
Proof.
  constructor.
  - intros ?; reflexivity.
  - intros ?; etransitivity; eauto.
Defined.

Program Definition chainProj {F} `{PDiagram F} n : PChain F -o> F n :=
  {| ofun_app := fun c => chain c n |}.
Next Obligation. firstorder. Qed.

Lemma chain_inv F `{PDiagram F} (c1 c2 : PChain F) :
  c1 =o= c2 -> forall n, chain c1 n =o= chain c2 n.
Proof. firstorder. Qed.


(** Product diagrams. *)
Section productPDiagram.
  Definition ProductTypeSequence (f1 f2 : nat -> Type) : nat -> Type :=
    fun n => prod (f1 n) (f2 n).

  Global Instance ProductOTypeSequence f1 f2
           {o1 : OTypeSequence f1} {o2 : OTypeSequence f2}
    : OTypeSequence (ProductTypeSequence f1 f2) :=
    fun n => OTpair _ _ _ _.

  Global Instance ProductPDiagram f1 f2
         `{PDiagram f1} `{PDiagram f2}
    : PDiagram (ProductTypeSequence f1 f2) :=
    fun n => pair_ofun (proj n ∘ fst_ofun) (proj n ∘ snd_ofun).
End productPDiagram.


Lemma product_proper A B `(OType A) `(OType B) (a c : A) (b d : B) :
  a =o= c ->
  b =o= d ->
  (a, b) =o= (c, d).
Proof. firstorder. Qed.

Lemma product_inv A B `(OType A) `(OType B) (a c : A) (b d : B) :
  (a, b) =o= (c, d) ->
  a =o= c /\ b =o= d.
Proof. firstorder. Qed.

(* Zip together two chains to form a single product chain. *)
Program Definition zipPChain {f1 f2} `{PDiagram f1} `{PDiagram f2} :
        PChain f1 * PChain f2 -o> PChain (ProductTypeSequence f1 f2) :=
  {| ofun_app :=
       fun p =>
         {| chain := fun n => (chain (fst p) n, chain (snd p) n) |} |}.
Next Obligation.
  apply product_proper.
  - destruct p; auto.
  - destruct p0; auto.
Qed.
Next Obligation. firstorder. Qed.

(* Unzip a product chain into two separate chains. *)
Program Definition unzipPChain {f1 f2} `{PDiagram f1} `{PDiagram f2} :
  PChain (ProductTypeSequence f1 f2) -o> PChain f1 * PChain f2 :=
  {| ofun_app :=
       fun f =>
         ({| chain := fun n => fst (chain f n) |},
          {| chain := fun n => snd (chain f n) |}) |}.
Next Obligation.
  destruct f; simpl; eapply product_inv in chainCondition0;
    apply chainCondition0.
Qed.
Next Obligation.
  destruct f; simpl; eapply product_inv in chainCondition0;
    apply chainCondition0.
Qed.
Next Obligation. intros f g Heq; split; intros n; apply Heq. Qed.

(* Zip and unzip are an isomorphism. *)
Lemma zip_unzip_PChain {f1 f2} `{PDiagram f1} `{PDiagram f2} :
  @zipPChain f1 f2 _ _ _ _ ∘ @unzipPChain f1 f2 _ _ _ _ =o= id_ofun.
Proof.
  split; intros c1 c2 Hleq n; apply Hleq.
Qed.

Lemma unzip_zip_PChain {f1 f2} `{PDiagram f1} `{PDiagram f2} :
  @unzipPChain f1 f2 _ _ _ _ ∘ zipPChain =o= id_ofun.
Proof.
  split; intros [] [] []; split; simpl; try apply H1; apply H2.
Qed.


(** Mapping a functor over a diagram. Can also be thought of
    postcomposition of a functor. *)
Section pDiagramMap.
  Definition typeSequenceMap (f : nat -> Type) `{PDiagram f}
             F `{func : Functor F} : nat -> Type :=
    fun n => F (f n) _.
  Global Instance oTypeSequenceMap (f : nat -> Type) `{PDiagram f}
         F `{func : Functor F}
    : OTypeSequence (typeSequenceMap f F) :=
    fun n => oF (f n) _.

  Global Program Instance pDiagramMap (f : nat -> Type) `{G : PDiagram f}
         F `{func : Functor F}
    : PDiagram (typeSequenceMap f F) :=
    fun n => fmap @@ proj n.
End pDiagramMap.


(* Mapping a natural transformation over a PChain. *)
Section pChainMap.
  Context f1 `{PDiagram f1} f2 `{PDiagram f2}
          (α : forall n, f1 n -o> f2 n)
          (* A specialized naturality condition. *)
          (α_natural : forall n, α n ∘ proj n =o= proj n ∘ α (S n)).

  Program Definition pChainMap : PChain f1 -o> PChain f2 :=
    {| ofun_app :=
         fun c =>
           {| chain := fun n => α n @@ (chain c n) |} |}.
  Next Obligation.
    assert (H1: proj n @@ (α (S n) @@ chain c (S n)) =
                (proj n ∘ α (S n)) @@ chain c (S n)) by auto.
    rewrite H1, <- α_natural; destruct c as [c Hc]; rewrite Hc; reflexivity.
  Qed.
  Next Obligation.
    intros ? ? Heq n; simpl in *;
      destruct (α n); apply ofun_Proper; apply Heq.
  Qed.
End pChainMap.


(** A continuous functor provides fold and unfold morphisms and a
    proof that they are an isomorphism. The type that they unfold to
    is specified by the functor, so it isn't guaranteed to be
    meaningful. E.g., the preorder and PER functors just use the
    identity morphism for fold and unfold, and the proof of
    isomorphism is trivial. *)
Section continuousFunctor.
  Context {F} `{Functor F}.

  Class UnfoldTypeF : Type :=
    unfoldTypeF : forall f `{PDiagram f}, Type.

  Class UnfoldOTypeF (U : UnfoldTypeF) : Type :=
    unfoldOTypeF :> forall f `{PDiagram f}, OType (unfoldTypeF f).

  Class UnfoldF (U : UnfoldTypeF) {UO : UnfoldOTypeF U} : Type :=
    unfoldF : forall f `{PDiagram f},
      PChain (typeSequenceMap f F) -o> unfoldTypeF f.

  Class FoldF (U : UnfoldTypeF) {UO : UnfoldOTypeF U} : Type :=
    foldF : forall f `{PDiagram f},
      unfoldTypeF f -o> PChain (typeSequenceMap f F).

  Class ContinuousFunctor (U : UnfoldTypeF) {UO : UnfoldOTypeF U}
        {fold : FoldF U} {unfold : UnfoldF U} : Prop :=
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
    | S n' => fmap @@ proj_n n'
    end.

  Global Instance FunctorOTypeSequence
    : OTypeSequence type_n := fun n => _.
  Global Instance FunctorPDiagram : PDiagram type_n := proj_n.
End functorPDiagram.


(* Lemma fmap_comp_pointwise A B C `{OType A} `{OType B} `{OType C} *)
(*       F `{Functor F} (f : A -p> B) (g : B -p> C) x : *)
(*   fmap @p@ g @p@ (fmap @p@ f @p@ x) =o= fmap @p@ (g ∘ f) @p@ x. *)
(* Proof. *)
(*   destruct H2. *)
(*   specialize (fmap_comp0 _ _ _ _ _ _ f g). *)
(*   destruct fmap_comp0. simpl in *. *)
(*   split; try apply H5; try apply H6; reflexivity. *)
(* Qed. *)


(** The constant functor for some fixed ordered type T. *)
Section constantFunctor.
  Context T `{OType T}.
  Definition ConstantF : TypeF := fun _ _ => T.
  Global Instance ConstantOTypeF : OTypeF ConstantF := fun _ _ => _.
  Global Instance ConstantFMap : FMap ConstantF :=
    fun _ _ _ _ => const_ofun id_ofun.
  Global Program Instance ConstantFunctor : Functor ConstantF.
  Solve Obligations with firstorder.
  Global Instance ConstantUnfoldTypeF : UnfoldTypeF := fun _ _ _ => T.
  Global Instance ConstantUnfoldOTypeF
    : UnfoldOTypeF ConstantUnfoldTypeF := fun _ _ _ => _.
  Global Program Instance ConstantUnfoldF : UnfoldF ConstantUnfoldTypeF :=
    fun _ _ _ => {| ofun_app := fun f => chain f 0 |}.
  Next Obligation. firstorder. Qed.
  Global Program Instance ConstantFoldF : FoldF ConstantUnfoldTypeF :=
    fun _ _ _ => {| ofun_app := fun x => {| chain := fun n => x |} |}.
  Next Obligation. reflexivity. Qed.
  Next Obligation. firstorder. Qed.
  Global Instance ConstantContinuousFunctor :
    ContinuousFunctor ConstantUnfoldTypeF.
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
    fun _ _ _ _ => id_ofun.
  Program Instance IdentityFunctor : Functor IdentityF.
  Solve Obligations with reflexivity.
  Global Instance IdentityUnfoldTypeF : UnfoldTypeF := fun f _ _ => PChain f.
  Global Instance IdentityUnfoldOTypeF
    : UnfoldOTypeF IdentityUnfoldTypeF := fun _ _ _ => _.
  Global Program Instance IdentityUnfoldF : UnfoldF IdentityUnfoldTypeF :=
    fun _ _ _ => id_ofun.
  Global Program Instance IdentityFoldF : FoldF IdentityUnfoldTypeF :=
    fun _ _ _ => id_ofun.
  Global Instance IdentityContinuousFunctor :
    ContinuousFunctor IdentityUnfoldTypeF.
  Proof. firstorder. Qed.
End identityFunctor.


(** The product functor. *)
Section productFunctor.
  Context F1 {oF1 : OTypeF F1} {fm1 : FMap F1} {func1 : Functor F1}
          {uF1 : UnfoldTypeF} {uoF1 : UnfoldOTypeF uF1}
          {foldF1 : FoldF uF1} {unfoldF1 : UnfoldF uF1}
          {cFunc1 : ContinuousFunctor uF1}
          F2 {oF2 : OTypeF F2} {fm2 : FMap F2} {func2 : Functor F2}
          {uF2 : UnfoldTypeF} {uoF2 : UnfoldOTypeF uF2}
          {foldF2 : FoldF uF2} {unfoldF2 : UnfoldF uF2}
          {cFunc2 : ContinuousFunctor uF2}.
  
  Definition ProductF : TypeF := fun X oX => prod (F1 X oX) (F2 X oX).

  Global Instance ProductOTypeF : OTypeF ProductF := fun _ _ => OTpair _ _ _ _.

  Global Program Instance ProductFMap : FMap ProductF :=
    fun _ _ _ _ =>
      {| ofun_app := fun f => pair_ofun (fmap @@ f ∘ fst_ofun)
                                     (fmap @@ f ∘ snd_ofun) |}.
  Next Obligation.
    intros f g Heq1 [x y] [z w] [Heq2 Heq3]; destruct fmap, fmap;
      split; try apply ofun_Proper; try apply ofun_Proper0; auto.
  Qed.

  Global Instance ProductFunctor : Functor ProductF.
  Proof.
    constructor.
    - intros A oA.
      split; simpl.
      + intros [] [] []; split; simpl; try rewrite H; try rewrite H0;
          destruct func1, func2; try rewrite fmap_id0;
            try rewrite fmap_id1; reflexivity.
      + split; destruct func1, func2; try rewrite fmap_id0;
          try rewrite fmap_id1; apply H.
    - intros A B C oA oB oC f g.
      split; split; simpl; destruct func1, func2;
        solve [rewrite fmap_comp0, H; reflexivity |
               rewrite fmap_comp1, H; reflexivity].
  Qed.

  Global Instance ProductUnfoldTypeF : UnfoldTypeF :=
  fun f _ _ => prod (@unfoldTypeF uF1 f _ _) (@unfoldTypeF uF2 f _ _).
  Global Instance ProductUnfoldOTypeF :
    UnfoldOTypeF ProductUnfoldTypeF := fun _ _ _ => _.

  Global Program Instance ProductUnfoldF : UnfoldF ProductUnfoldTypeF :=
    fun f _ _ =>
      pair_ofun (unfoldF f ∘ fst_ofun) (unfoldF f ∘ snd_ofun) ∘ unzipPChain.
  Global Program Instance ProductFoldF : FoldF ProductUnfoldTypeF :=
    fun f _ _ =>
      zipPChain ∘ pair_ofun (foldF f ∘ fst_ofun) (foldF f ∘ snd_ofun).


  Lemma asdf A B C D E `{OType A} `{OType B} `{OType C} `{OType D}
        `{OType E} (f : A -o> B) (g : B -o> C) (h : C -o> D) (k : D -o> E) :
    (k ∘ h) ∘ (g ∘ f) =o= k ∘ (h ∘ g) ∘ f.
  Proof. split; intros ? ? Hleq; rewrite Hleq; reflexivity. Qed.

  Lemma asdf2 A B C `{OType A} `{OType B} `{OType C} (f : A -o> B)
        (g : B -o> C) (h : C -o> B) (k : B -o> A) :
    h ∘ g =o= id_ofun ->
    k ∘ (h ∘ g) ∘ f =o= k ∘ f.
  Proof.
    intros Hid; rewrite Hid; rewrite id_compose_ofun; reflexivity.
  Qed.

  Lemma asdf' {A B C D E F} `{OType A} `{OType B} `{OType C}
        `{OType D} `{OType E} `{OType F}
        (f : A -o> C) (g : B -o> D) (h : C -o> E) (k : D -o> F) :
    pair_ofun (h ∘ fst_ofun) (k ∘ snd_ofun) ∘
              pair_ofun (f ∘ fst_ofun) (g ∘ snd_ofun) =o=
    pair_ofun (h ∘ f ∘ fst_ofun) (k ∘ g ∘ snd_ofun).
  Proof.
    split; intros [] [] [Hleq1 Hleq2];rewrite Hleq1, Hleq2; reflexivity.
  Qed.

  Global Instance ProductContinuousFunctor :
    ContinuousFunctor ProductUnfoldTypeF.
  Proof.
    constructor; intros f o G.
    - unfold unfoldF, ProductUnfoldF, foldF, ProductFoldF.
      rewrite asdf.
      rewrite unzip_zip_PChain.
      rewrite id_compose_ofun.
      etransitivity. apply asdf'.
      destruct cFunc1. rewrite unfold_fold_id0. rewrite compose_id_ofun.
      destruct cFunc2. rewrite unfold_fold_id1. rewrite compose_id_ofun.
      apply pair_fst_snd_eta.
    - unfold unfoldF, ProductUnfoldF, foldF, ProductFoldF.
      rewrite asdf. rewrite asdf2.
      + 
        
admit.
      + etransitivity. apply asdf'.

      destruct cFunc1. rewrite fold_unfold_id0. rewrite compose_id_ofun.
      destruct cFunc2. rewrite fold_unfold_id1. rewrite compose_id_ofun.
      apply pair_fst_snd_eta.
  Admitted.

End productFunctor.


Definition fmapRel {A B} `{OType A} `{OType B} (f : A -o> B)
           (R : relation A) : relation B :=
  fun y1 y2 => exists x1 x2, f @@ x1 =o= y1 /\ f @@ x2 =o= y2 /\ R x1 x2.


Class PreOrder {A} `{OType A} (R : relation A) : Prop :=
  { Proper_PreOrder :> Proper (oeq ==> oeq ==> oleq) R
  ; Reflexive_PreOrder :> Reflexive R
  ; Transitive_PreOrder :> Transitive R }.


(** The preorder functor. *)
Section preorderFunctor.
  Context F {oF : OTypeF F} {fm : FMap F} {func : Functor F}.

  Definition PreOrderF : TypeF := fun X oX => {R : relation (F _ _) | PreOrder R}.

  Global Instance PreOrderOTypeF : OTypeF PreOrderF := fun _ _ => _.

  (* TODO: this isn't right.. I think we need a different notion of
     reflexive transitive closure (one that is just reflexive wrt
     oeq). *)
  Instance Proper_clos_refl_trans {A} `{OType A} (R : relation A) :
    Proper (oeq ==> oeq ==> oleq) R ->
    Proper (oeq ==> oeq ==> oleq) (clos_refl_trans R).
  Proof.
    intros Hprop x y Heq1 z w Heq2 Hclos.
    revert y w Heq1 Heq2.
    induction Hclos; intros.
    - apply rt_step; rewrite <- Heq1, <- Heq2; auto.
    - admit.
    (* - apply rt_step; rewrite <- Heq1, <- Heq2; apply Hrefl. *)
    - apply rt_trans with y. apply IHHclos1; auto; reflexivity.
      apply IHHclos2; auto; reflexivity.
  Admitted.

  Instance Proper_fmapRel {A B} `{OType A} `{OType B}
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
    clos_refl_trans (fmapRel (fmap @@ f) (proj1_sig R)).
  Next Obligation.
    constructor.
    - apply Proper_clos_refl_trans, Proper_fmapRel;
        destruct R as [R HR]; destruct HR; auto.
    - intros ?; apply rt_refl.
    - intros ?; apply rt_trans.
  Qed.

  Admit Obligations.

  Instance Proper_clos_trans {A} `{OType A} {R : relation A} :
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

  Global Program Instance PreOrderFMap : FMap PreOrderF :=
    fun _ _ _ _ =>
      {| ofun_app := fun f => {| ofun_app := fun r => fmapPreOrder f r |} |}.
  Next Obligation.
    intros R1 R2 Heq1 x y Heq2.
    simpl in *.
    revert R2 Heq1.
    induction Heq2; intros.
    - apply rt_step. admit.
    - admit.
    - eapply rt_trans; eauto.
  Admitted.
  Next Obligation.
    intros x y Heq1 R1 R2 Heq2 z w Hclos. simpl in *.
    revert y Heq1 R2 Heq2.
    induction Hclos; intros.
    - admit.
    - admit.
    - eapply rt_trans; eauto.
  Admitted.


Admit Obligations.
  Global Program Instance PreOrderFunctor : Functor PreOrderF.
  Next Obligation.
    split; unfold oleq; simpl.
    - intros R1 R2 Hleq. unfold fmapPreOrder. unfold oleq. simpl.
      unfold oleq in Hleq. simpl in *.
      unfold oleq. simpl.
      intros x y Hclos.
      admit.
    - admit.
  Admitted.

  Next Obligation.
    split; simpl.
    - unfold oleq. simpl.
      intros R1 R2 Hleq. unfold oleq; simpl.
      unfold oleq; simpl.
      intros x y Hclos.
      revert R2 Hleq.
      induction Hclos; intros.
      + admit.
      + admit.
      + eapply rt_trans; eauto.
    - intros R1 R2 Hleq1.
      intros x y Hclos; simpl in *.
      revert R2 Hleq1; induction Hclos; intros.
      + admit.
      + admit.
      + eapply rt_trans; eauto.
  Admitted.

  Global Instance PreOrderUnfoldTypeF : UnfoldTypeF :=
    fun f _ _ => PChain (typeSequenceMap f PreOrderF).
  Global Instance PreOrderUnfoldOTypeF :
    UnfoldOTypeF PreOrderUnfoldTypeF := fun _ _ _ => _.
  Global Instance PreOrderUnfoldF : UnfoldF PreOrderUnfoldTypeF :=
    fun _ _ _ => id_ofun.
  Global Instance PreOrderFoldF : FoldF PreOrderUnfoldTypeF :=
    fun _ _ _ => id_ofun.
  Global Instance PreOrderContinuousFunctor :
    ContinuousFunctor PreOrderUnfoldTypeF.
  Proof. constructor; intros; apply id_compose_ofun. Qed.
End preorderFunctor.


Class PER {A} `{OType A} (R : relation A) : Prop :=
  { Proper_PER :> Proper (oeq ==> oeq ==> oleq) R
  ; Symmetric_PER :> Symmetric R
  ; Transitive_PER :> Transitive R }.


(** The PER functor. *)
Section perFunctor.
  Context F {oF : OTypeF F} {fm : FMap F} {func : Functor F}.

  Definition PERF : TypeF := fun X oX => {R : relation (F _ _) | PER R}.

  Global Instance PEROTypeF : OTypeF PERF := fun _ _ => _.

  Program Definition fmapPER {A B} `{OType A} `{OType B} (f : A -o> B)
          (R : PERF A _) : PERF B _ :=
    clos_trans (fmapRel (fmap @@ f) (proj1_sig R)).
  Admit Obligations.

  Global Program Instance PERFMap : FMap PERF :=
    fun _ _ _ _ =>
      {| ofun_app := fun f => {| ofun_app := fun r => fmapPER f r |} |}.
  Admit Obligations.

  Global Program Instance PERFunctor : Functor PERF.
  Admit Obligations.

  Global Instance PERUnfoldTypeF : UnfoldTypeF :=
    fun f _ _ => PChain (typeSequenceMap f PERF).
  Global Instance PERUnfoldOTypeF :
    UnfoldOTypeF PERUnfoldTypeF := fun _ _ _ => _.
  Global Program Instance PERUnfoldF : UnfoldF PERUnfoldTypeF :=
    fun _ _ _ => id_ofun.
  Global Program Instance PERFoldF : FoldF PERUnfoldTypeF :=
    fun _ _ _ => id_ofun.
  Global Instance PERContinuousFunctor : ContinuousFunctor PERUnfoldTypeF.
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

  Fixpoint tree_size {A} (t : Tree A) :=
    match t with
    | Leaf _ => 1
    | Node t1 t2 => 1 + tree_size t1 + tree_size t2
    end.

  (* Fixpoint tree_oleq' {A} `{OType A} (t1 t2 : Tree A) : Prop := *)
  (*   match t1, t2 with *)
  (*   | Leaf x, Leaf y => x <o= y *)
  (*   | Node t11 t12, Node t21 t22 => *)
  (*     tree_oleq t11 t21 /\ tree_oleq t12 t22 *)
  (*   | _, _ => False *)
  (*   end. *)

  (* Lemma tree_oleq_equivalent {A} `{OType A} (t1 t2 : Tree A) : *)
  (*   tree_oleq t1 t2 <-> tree_oleq' t1 t2. *)
  (* Proof. *)
  (*   split; intro Hleq. *)
  (*   - induction Hleq; simpl; auto. *)
  (*   - revert t2 Hleq. induction t1; intros. *)
  (*     + destruct t2; try contradiction; constructor; auto. *)
  (*     + destruct t2; try contradiction. *)
  (*       destruct Hleq as [H0 H1]. *)
  (*       constructor; auto. *)
  (* Qed. *)

  (* Instance Reflexive_tree_oleq {A} `{OType A} : Reflexive tree_oleq. *)
  (* Proof. *)
  (*   intros t; induction t; firstorder; simpl; reflexivity. *)
  (* Qed. *)

  Instance Reflexive_tree_oleq {A} `{OType A} : Reflexive tree_oleq.
  Proof. intro x; induction x; constructor; auto; reflexivity. Qed.

  Instance Transitive_tree_oleq {A} `{OType A} : Transitive tree_oleq.
  Proof.
    intros x y z Hxy Hyz. admit.
  Admitted.

  Global Program Instance OTtree A `(OType A) : OType (Tree A) :=
    {| oleq := tree_oleq |}.
  Next Obligation.
  constructor.
  - apply Reflexive_tree_oleq.
  - apply Transitive_tree_oleq.
  Qed.

  Instance Proper_Leaf {A} `{OType A} :
    Proper (oleq ==> oleq) Leaf.
  Proof. constructor; auto. Qed.
  
  Instance Proper_Node {A} `{OType A} :
    Proper (oleq ==> oleq ==> oleq) Node.
  Proof. constructor; auto. Qed.

  Fixpoint tree_fmap {A B} `{OType A} `{OType B} (f : A -o> B)
           (t : Tree A) : Tree B :=
    match t with
    | Leaf x => Leaf (f @@ x)
    | Node t1 t2 => Node (tree_fmap f t1) (tree_fmap f t2)
    end.

  Program Definition Tree_fmap {A B} `{OType A} `{OType B} (f : A -o> B)
    : Tree A -o> Tree B :=
    {| ofun_app := fun t => tree_fmap f t |}.
  Admit Obligations.

  Lemma tree_fmap_id A `{OType A} x :
    tree_fmap id_ofun x =o= x.
  Proof.
    induction x.
    - reflexivity.
    - simpl; rewrite IHx1, IHx2; reflexivity.
  Qed.

  Lemma TreeFMap_id A `{OType A} :
    Tree_fmap id_ofun =o= id_ofun.
  Proof.
    generalize (tree_fmap_id A).
    intros H0.
    unfold Tree_fmap. simpl in *.
    split; simpl; intros t1 t2 Hleq.
    (* rewrite H0; auto. *)
    admit.
    admit.
  Admitted.

  Lemma TreeFMap_comp A B C `{OType A} `{OType B} `{OType C}
        (f : A -o> B) (g : B -o> C) :
    Tree_fmap (g ∘ f) =o= Tree_fmap g ∘ Tree_fmap f.
  Admitted.

  Fixpoint unLeaf {A} (t : Tree A) : A :=
    match t with
    | Leaf x => x
    | Node t1 _ => unLeaf t1 (* shouldn't happen *)
    end.

  Instance Proper_unLeaf {A} `{OType A} :
    Proper (oleq ==> oleq) unLeaf.
  Proof. intros ? ? Heq; induction Heq; auto. Qed.

  Definition unLeaf' {A} `{OType A} : Tree A -o> A :=
    {| ofun_app := unLeaf; ofun_Proper := Proper_unLeaf |}.

  Fixpoint unNodeLeft {A} (t : Tree A) : Tree A :=
    match t with
    | Leaf _ => t (* shouldn't happen *)
    | Node t1 _ => t1
    end.

  Instance Proper_unNodeLeft {A} `{OType A} :
    Proper (oleq ==> oleq) unNodeLeft.
  Proof.
    intros ? ? Heq; induction Heq; auto; simpl; rewrite H0; reflexivity.
  Qed.

  Definition unNodeLeft' {A} `{OType A} : Tree A -o> Tree A :=
    {| ofun_app := unNodeLeft; ofun_Proper := Proper_unNodeLeft |}.

  Fixpoint unNodeRight {A} (t : Tree A) : Tree A :=
    match t with
    | Leaf _ => t (* shouldn't happen *)
    | Node _ t2 => t2
    end.

  Instance Proper_unNodeRight {A} `{OType A} :
    Proper (oleq ==> oleq) unNodeRight.
  Proof.
    intros ? ? Heq; induction Heq; auto; simpl; rewrite H0; reflexivity.
  Qed.

  Definition unNodeRight' {A} `{OType A} : Tree A -o> Tree A :=
    {| ofun_app := unNodeRight; ofun_Proper := Proper_unNodeRight |}.

End tree.


Section mapTreePDiagram.
  Definition mapTreeTypeSequence f `{PDiagram f} : nat -> Type :=
    fun n => Tree (f n).
  Global Instance MapTreeOTypeSequence f `{PDiagram f}
    : OTypeSequence (mapTreeTypeSequence f) := fun n => _.
  Global Instance MapTreePDiagram f `{PDiagram f}
    : PDiagram (mapTreeTypeSequence f) := fun n => Tree_fmap (proj n).
End mapTreePDiagram.


Section treePChain.
  
  Program Definition unLeafPChain {f} `{PDiagram f}
  : PChain (mapTreeTypeSequence f) -o> PChain f :=
    pChainMap (mapTreeTypeSequence f) f
              (fun _ => {| ofun_app := fun x => unLeaf' @@ x |}) _.
  Next Obligation. apply Proper_unLeaf. Qed.
  Next Obligation.
    unfold oeq, oleq; split; simpl; intros ? ? Heq;
      induction Heq; simpl; auto; rewrite H0; reflexivity.
  Qed.

  Program Definition unNodeLeftPChain {f} `{PDiagram f}
  : PChain (mapTreeTypeSequence f) -o> PChain (mapTreeTypeSequence f) :=
    pChainMap (mapTreeTypeSequence f) (mapTreeTypeSequence f)
              (fun _ => {| ofun_app := fun x => unNodeLeft' @@ x |}) _.
  Next Obligation. apply Proper_unNodeLeft. Qed.
  Next Obligation.
    split; simpl.
    - intros c1 c2 Heq.
      unfold oleq; simpl.
      admit.
    - intros c1 c2 Heq.
      unfold oleq. simpl.
      admit.
  Admitted.

  Program Definition unNodeRightPChain {f} `{PDiagram f}
  : PChain (mapTreeTypeSequence f) -o> PChain (mapTreeTypeSequence f) :=
    pChainMap (mapTreeTypeSequence f) (mapTreeTypeSequence f)
              (fun _ => {| ofun_app := fun x => unNodeRight' @@ x |}) _.
  Next Obligation. apply Proper_unNodeRight. Qed.
  Next Obligation.
    split; simpl.
    - intros c1 c2 Hleq.
      unfold oleq; simpl.
      admit.
    - intros c1 c2 Hleq.
      unfold oleq; simpl.
      admit.
  Admitted.


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

  Program Fixpoint treeUnfold_f {f} `{PDiagram f}
          (c : PChain (mapTreeTypeSequence f))
          {measure (tree_size (chain c 0))}
    : Tree (PChain f) :=
    match chain c 0 with
    | Leaf _ => Leaf (unLeafPChain @@ c)
    | Node _ _ => Node (treeUnfold_f (unNodeLeftPChain @@ c))
                      (treeUnfold_f (unNodeRightPChain @@ c))
    end.
  Next Obligation. simpl; omega. Qed.
  Next Obligation. simpl; omega. Qed.

  Program Definition treeUnfold {f} `{PDiagram f}
    : PChain (mapTreeTypeSequence f) -o> Tree (PChain f) :=
    {| ofun_app := treeUnfold_f |}.
  Next Obligation.
    intros c1 c2 Hleq.
    unfold oleq; simpl.
    admit.
  Admitted.

  Lemma tree_fold_unfold {f} `{PDiagram f} :
    treeFold ∘ treeUnfold =o= id_ofun.
  Admitted.

  Lemma tree_unfold_fold {f} `{PDiagram f} :
    treeUnfold ∘ treeFold =o= id_ofun.
  Admitted.

End treePChain.


(** The tree functor. *)
Section treeFunctor.
  Context F {oF : OTypeF F} {fm : FMap F} {func : Functor F}
          {uF : UnfoldTypeF} {uOF : UnfoldOTypeF uF}
          {fF : FoldF uF} {ufF : UnfoldF uF}.

  Definition TreeF : TypeF := fun X oX => Tree (F X oX).

  Global Instance TreeOTypeF : OTypeF TreeF := fun _ _ => _.

  Global Program Instance TreeFMap : FMap TreeF :=
    fun _ _ _ _ => _.
  Admit Obligations.

  Global Program Instance TreeFunctor : Functor TreeF.
  Admit Obligations.

  Global Instance TreeUnfoldTypeF : UnfoldTypeF :=
  fun f _ _ => Tree (@unfoldTypeF uF f _ _).
  Global Instance TreeUnfoldOTypeF :
    UnfoldOTypeF TreeUnfoldTypeF := fun _ _ _ => _.
  Global Program Instance TreeFoldF : FoldF TreeUnfoldTypeF := _.
    (* fun f _ _ => *)
    (*   treeFold ∘ (Tree_fmap @@ foldF f). *)
  Admit Obligations.
  Global Program Instance TreeUnfoldF : UnfoldF TreeUnfoldTypeF := _.
  Admit Obligations.
  Global Instance TreeContinuousFunctor : ContinuousFunctor TreeUnfoldTypeF.
  Proof. Admitted.

End treeFunctor.


(** The recursive type for memory stores. *)
Section mem.
  (* Context ptr `{OType ptr}. *)
  (* Context value `{OType value}. *)
  (* Definition ptrmap := ptr -> value. *)

  Context Z `{OType Z}.

  Definition memF : TypeF :=
    ProductF
      (ConstantF Z)
      (TreeF (ProductF (PERF IdentityF) (PreOrderF IdentityF))).

  Definition MemDiag : nat -> Type := type_n memF.

  Definition Mem := PChain (type_n memF).

  (* Definition MemPERDiag := typeSequenceMap MemDiag (PERF IdentityF). *)
  (* Definition MemPER := PChain MemPERDiag. *)

  (* Definition MemPreOrderDiag := typeSequenceMap MemDiag (PreOrderF IdentityF). *)
  (* Definition MemPreOrder := PChain MemPreOrderDiag. *)
End mem.
