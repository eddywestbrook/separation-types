Require Export SepTypes.OrderedType.
Require Export SepTypes.DownSet.
Require Export SepTypes.Monad.

Import ListNotations.


(***
 *** The Trace Monad = Final Algebra of Sets of Traces
 ***)

(* A trace computation starts from any given input state, and generates a trace
of intermediate states followed by an optional final state (if it terminates) *)
Definition TraceM St `{OType St} A `{OType A} :=
  FunGraph St (list St * option (A * St)).

Instance OTypeF_TraceM St `{OType St} : OTypeF (TraceM St) := fun _ _ => _.

Instance MonadOps_TraceM St `{OType St} : MonadOps (TraceM St) :=
  {| returnM :=
       fun _ _ x =>
         (* For each input st, return x as the output and st as the final state,
         with no intermediate states *)
         lambdaDownSet (fun st => downClose ([], Some (x, st)));
     bindM :=
       fun _ _ _ _ m f =>
         (* For each input state st... *)
         lambdaDownSet
           (fun st =>
              bindDownSet
                (* Pass st into m *)
                (applyDownSet m st)
                (fun trace_out1 =>
                   (* Get (trace1, out) = (m st), and test if out is a Some *)
                   optElim
                     (fun a_st1 =>
                        (* If (m st) = (trace1, Some (a, st2)), then get
                           (trace2, out) = (f a st), and return the result
                           (trace1 ++ trace2, out) *)
                        mapDownSet
                          (fun trace_out2 =>
                             (fst trace_out1 ++ fst trace_out2, snd trace_out2))
                          (applyDownSet (f (fst a_st1)) (snd a_st1)))
                     (* Otherwise, m did not terminate, so we don't call f at
                     all, and just return (trace1, None) *)
                     (downClose (fst trace_out1, None))
                     (* (snd trace_out1) is the option output of (m st) *)
                     (snd trace_out1)))
  |}.

Instance Monad_TraceM St `{OType St} : Monad (TraceM St).
Proof.
  constructor.
  { intros. intros a1 a2 Ra. simpl. apply Proper_lambdaDownSet. intro st.
    rewrite Ra. reflexivity. }
  { intros. intros m1 m2 Rm f1 f2 Rf. apply Proper_lambdaDownSet. intro st.
    rewrite Rm. apply Proper_bindDownSet; try reflexivity. intro trace_out1.
    apply (Proper_optElim_eq _ _); try reflexivity.
    intro a_st1. apply Proper_bindDownSet; try reflexivity.
    apply Proper_applyDownSet; [ apply Rf | reflexivity ]. }
  { intros. simpl.
    rewrite <- (downSetEta (f a)).
    apply Proper_lambdaDownSet_equiv. apply funOExt; intro st.
    rewrite downSetBeta; [ | intros st1 st2 Rst; rewrite Rst; reflexivity ].
    rewrite DownSet_return_bind.
    - simpl. unfold mapDownSet.
      etransitivity; [ | apply DownSet_bind_return ].
      apply Proper_bindDownSet_equiv; try reflexivity.
      apply funOExt. intros [ tr ret ]. reflexivity.
    - intros tr_out1 tr_out2 Rtr_out.
      eapply Proper_optElim; try (rewrite Rtr_out; reflexivity).
      intros a_st1 a_st1' Ra_st1.
      apply Proper_bindDownSet; [ rewrite Ra_st1; reflexivity | ].
      intro f_tr_out. rewrite Rtr_out. reflexivity. }
  { intros. simpl. rewrite <- (downSetEta m).
    apply Proper_lambdaDownSet_equiv. apply funOExt; intro st.
    etransitivity; [ | apply DownSet_bind_return ].
    f_equiv. apply funOExt. intros [ tr [[ a st'] | ]]; [ | reflexivity ].
    simpl. unfold mapDownSet. rewrite downSetBeta.
    - rewrite DownSet_return_bind; [ simpl; rewrite app_nil_r; reflexivity | ].
      intros tr_ret1 tr_ret2 Rtr_ret. rewrite Rtr_ret. reflexivity.
    - intros st1 st2 Rst. rewrite Rst. reflexivity. }
  { intros.
