Require Import SepTypes.OrderedType SepTypes.OFuns SepTypes.Functor SepTypes.PChain.

Open Scope ofun_scope.


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


(** The tree functor. *)
Section treeFunctor.
  Context F {oF : OTypeF F} {fm : FMap F} {func : Functor F}
          {uF : UnfoldTypeF F} {uOF : UnfoldOTypeF F}
          {fF : FoldF F} {ufF : UnfoldF F}
          {cFunc : ContinuousFunctor F}.

  Definition TreeF : TypeF := fun X oX => Tree (F X oX).

  Global Instance TreeOTypeF : OTypeF TreeF := fun _ _ => _.

  Global Instance TreeFMap : FMap TreeF :=
    fun _ _ _ _ => fun f => Tree_fmap (fmap f).

  Global Program Instance TreeFunctor : Functor TreeF.
  Next Obligation.
    unfold fmap, TreeFMap; destruct func.
    rewrite fmap_id; apply Tree_fmap_id.
  Qed.
  Next Obligation.
    unfold fmap, TreeFMap; destruct func.
    rewrite fmap_comp; apply Tree_fmap_comp.
  Qed.
End treeFunctor.


(** Operations and proofs related to chains of trees. *)
Section treePChain.
  Definition treeDiag f `{PDiagram f} := typeSequenceMap f (TreeF IdentityF).

  Program Definition unLeafPChain {f} `{PDiagram f}
  : PChain (treeDiag f) -o> PChain f := pChainMap (treeDiag f) f
              (fun _ => {| ofun_app := fun x => unLeaf' @@ x |}) _.
  Next Obligation.
    unfold oeq, oleq; split; simpl; intros ? ? Heq;
      induction Heq; simpl; auto; rewrite H0; reflexivity.
  Qed.

  Program Definition unNodeLeftPChain {f} `{PDiagram f}
    : PChain (treeDiag f) -o> PChain (treeDiag f) :=
    pChainMap (treeDiag f) (treeDiag f)
              (fun _ => {| ofun_app := fun x => unNodeLeft' @@ x |}) _.
  Next Obligation.
    split; simpl; intros c1 c2 Hleq; induction Hleq;
      try apply Proper_tree_fmap; auto; constructor;
        rewrite H0; reflexivity.
  Qed.

  Program Definition unNodeRightPChain {f} `{PDiagram f}
    : PChain (treeDiag f) -o> PChain (treeDiag f) :=
    pChainMap (treeDiag f) (treeDiag f)
              (fun _ => {| ofun_app := fun x => unNodeRight' @@ x |}) _.
  Next Obligation.
    split; simpl; intros c1 c2 Hleq; induction Hleq;
      try apply Proper_tree_fmap; auto; constructor;
        rewrite H0; reflexivity.
  Qed.

  Lemma unNodeLeftPChain_oleq {f} `{PDiagram f} (c1 c2 : PChain (treeDiag f)) :
    c1 <o= c2 ->
    unNodeLeftPChain @@ c1 <o= unNodeLeftPChain @@ c2.
  Proof.
    intros Hleq n; simpl; specialize (Hleq n);
      destruct (chain c1 n), (chain c2 n);
      inversion Hleq; subst; auto.
  Qed.

  Lemma unNodeRightPChain_oleq {f} `{PDiagram f} (c1 c2 : PChain (treeDiag f)) :
    c1 <o= c2 ->
    unNodeRightPChain @@ c1 <o= unNodeRightPChain @@ c2.
  Proof.
    intros Hleq n; simpl; specialize (Hleq n);
      destruct (chain c1 n), (chain c2 n);
      inversion Hleq; subst; auto.
  Qed.

  Program Definition treeFold {f} `{PDiagram f} :
    Tree (PChain f) -o> PChain (treeDiag f) :=
    {| ofun_app :=
         fun t =>
           {| chain := fun n => Tree_fmap (chainProj n) @@ t |} |}.
  Next Obligation.
    induction t; simpl.
    - destruct a; apply (Proper_oeq_oleq_op1 _ _ _ Proper_Leaf);
        apply chainCondition.
    - apply (Proper_oeq_oleq_op2 _ _ _ _ Proper_Node); auto.
  Qed.
  Next Obligation.
    intros x y Heq n. simpl.
    induction Heq; simpl in *.
    - specialize (H0 n). apply Proper_Leaf; auto.
    - apply Proper_Node; auto.
  Qed.

  Fixpoint treeUnfold_f_aux {f} `{PDiagram f}
           (c : PChain (treeDiag f))
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
           (c : PChain (treeDiag f))
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
    : PChain (treeDiag f) -o> Tree (PChain f) :=
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

  Lemma isLeaf_chain f `{PDiagram f} (c : PChain (treeDiag f)) n :
    isLeaf (chain c 0) -> isLeaf (chain c n).
  Proof.
    intros Hleaf; inversion Hleaf.
    destruct c; simpl in *.
    induction n.
    - rewrite <- H1; constructor.
    - specialize (chainCondition n).
      generalize (isLeaf_oleq _ (chain n)
                              (tree_fmap (proj n) (chain (S n)))
                              IHn (proj1 chainCondition)); intros Hleaf'.
      apply isLeaf_fmap in Hleaf'; auto.
  Qed.

  Lemma isNode_chain f `{PDiagram f} (c : PChain (treeDiag f)) n :
    isNode (chain c 0) -> isNode (chain c n).
  Proof.
    intros Hnode; inversion Hnode.
    destruct c; simpl in *.
    induction n.
    - rewrite <- H1; constructor.
    - specialize (chainCondition n).
      generalize (isNode_oleq _ (chain n)
                              (tree_fmap (proj n) (chain (S n)))
                              IHn (proj1 chainCondition)); intros Hnode'.
      apply isNode_fmap in Hnode'; auto.
  Qed.

  Lemma tree_fold_unfold f `{PDiagram f} :
    treeFold ∘ treeUnfold =o= id_ofun.
  Proof.
    split; simpl.
    - intros c1 c2 Hleq n. unfold oleq; simpl.
      unfold treeUnfold_f.
      transitivity (chain c1 n).
      + clear Hleq c2; remember (chain c1 0) as m; revert c1 Heqm.
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
      + clear Hleq c1; unfold treeUnfold_f; remember (chain c2 0) as m.
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


(** The tree continuous functor. *)
Section continuousTreeFunctor.
  Context F {oF : OTypeF F} {fm : FMap F} {func : Functor F}
          {uF : UnfoldTypeF F} {uOF : UnfoldOTypeF F}
          {fF : FoldF F} {ufF : UnfoldF F}
          {cFunc : ContinuousFunctor F}.

  Global Instance TreeUnfoldTypeF : UnfoldTypeF (TreeF F) :=
  fun f _ _ => Tree (@unfoldTypeF F uF f _ _).
  Global Instance TreeUnfoldOTypeF : UnfoldOTypeF (TreeF F) := fun _ _ _ => _.
  Global Instance TreeFoldF : FoldF (TreeF F) :=
    fun f _ _ => treeFold ∘ Tree_fmap (foldF f).
  Global Instance TreeUnfoldF : UnfoldF (TreeF F) :=
    fun f _ _ => Tree_fmap (unfoldF f) ∘ treeUnfold.
  Global Instance TreeContinuousFunctor : ContinuousFunctor (TreeF F).
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
      destruct cFunc. rewrite unfold_fold_id.
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
      destruct cFunc. rewrite fold_unfold_id.
      apply Tree_fmap_id.
  Qed.
End continuousTreeFunctor.
