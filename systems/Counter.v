Require Import Verdi.
Require Import HandlerMonad.
Require Import UpdateLemmas.
Require Import Cheerios.Types.
Local Arguments update {_} {_} {_} _ _ _ _ : simpl never.

Set Implicit Arguments.

Section Counter.
  Inductive Name := primary | backup.
  Definition Name_eq_dec : forall x y : Name, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition name_serialize (n: Name) : list bool :=
    match n with
    | primary => true :: nil
    | backup => false :: nil
    end.

  Definition name_deserialize (bin: list bool) : option (Name * list bool) :=
    match bin with
    | nil => None
    | h :: t =>
      match h with
      | true => Some(primary, t)
      | false => Some(backup, t)
      end
    end.

  Lemma name_serialize_reversible: forall (n: Name) (bin: list bool),
      name_deserialize ((name_serialize n) ++ bin) = Some (n, bin).
  Proof.
    unfold name_deserialize, name_serialize.
    intros.
    destruct n; reflexivity.
  Qed.

  Instance Name_Serializer: Serializer Name :=
    {
      serialize := name_serialize;
      deserialize := name_deserialize;
      Serialize_reversible := name_serialize_reversible
    }.

  Inductive Msg := inc | ack.
  Definition Msg_eq_dec : forall x y : Msg, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition msg_serialize (m: Msg) : list bool :=
    match m with
    | inc => true :: nil
    | ack => false :: nil
    end.

  Definition msg_deserialize (bin: list bool) : option (Msg * list bool) :=
    match bin with
    | nil => None
    | h :: t =>
      match h with
      | true => Some(inc, t)
      | false => Some(ack, t)
      end
    end.

  Lemma msg_serialize_reversible: forall (m: Msg) (bin: list bool),
      msg_deserialize ((msg_serialize m) ++ bin) = Some (m, bin).
  Proof.
    unfold msg_deserialize, msg_serialize.
    intros.
    destruct m; reflexivity.
  Qed.

  Instance Msg_Serializer: Serializer Msg :=
    {
      serialize := msg_serialize;
      deserialize := msg_deserialize;
      Serialize_reversible := msg_serialize_reversible
    }.

  Inductive Input := request_inc.
  Definition Input_eq_dec : forall x y : Input, {x = y} + {x <> y}.
    destruct x,y. auto.
  Defined.

  Definition input_serialize (i: Input) : list bool :=
    nil.

  Definition input_deserialize (bin: list bool) : option (Input * list bool) :=
    Some(request_inc, bin).

  Lemma input_serialize_reversible: forall (i: Input) (bin: list bool),
      input_deserialize ((input_serialize i) ++ bin) = Some (i, bin).
  Proof.
    unfold input_deserialize, input_serialize.
    intros; simpl.
    destruct i; auto.
  Qed.

  Instance Input_Serializer: Serializer Input :=
    {
      serialize := input_serialize;
      deserialize := input_deserialize;
      Serialize_reversible := input_serialize_reversible;
    }.

  Inductive Output := inc_executed.
  Definition Output_eq_dec : forall x y : Output, {x = y} + {x <> y}.
    destruct x,y. auto.
  Defined.

  Definition output_serialize (o: Output) : list bool :=
    nil.

  Definition output_deserialize (bin: list bool) : option (Output * list bool) :=
    Some(inc_executed, bin).

  Lemma output_serialize_reversible: forall (o: Output) (bin: list bool),
      output_deserialize ((output_serialize o) ++ bin) = Some (o, bin).
  Proof.
    unfold output_deserialize, output_serialize.
    intros; simpl.
    destruct o; auto.
  Qed.

  Instance Output_Serializer: Serializer Output :=
    {
      serialize := output_serialize;
      deserialize := output_deserialize;
      Serialize_reversible := output_serialize_reversible;
    }.

  Definition Data := nat.

  Definition init_Data := 0.

  Definition Handler (S : Type) := GenHandler (list bool * list bool) S Output unit.

  Definition PrimaryNetHandler (mBits : list bool) : Handler Data :=
    match (deserialize mBits) with
    | None => nop
    | Some (m, rest) =>
      match m with
      | ack => write_output inc_executed
      | _ => nop
      end
    end.

  Definition PrimaryInputHandler (iBits : list bool) : Handler Data :=
    match (deserialize iBits) with
    | None => nop
    | Some (i, rest) =>
      match i with
      | request_inc => modify S ;; send ((serialize backup), (serialize inc))
      end
    end.

  Definition BackupNetHandler (mBits : list bool) : Handler Data :=
    match (deserialize mBits) with
    | None => nop
    | Some (m, rest) =>
      match m with
      | inc => modify S ;; send ((serialize primary), (serialize ack))
      | _ => nop
      end
    end.

  Definition BackupInputHandler (iBits : list bool) : Handler Data := nop.

  Definition NetHandler (meBits : list bool) (mBits : list bool) : Handler Data :=
    match (deserialize meBits) with
    | None => nop
    | Some (me, rest) =>
      match me with
      | primary => PrimaryNetHandler mBits
      | backup => BackupNetHandler mBits
      end
    end.

  Definition InputHandler (meBits : list bool) (iBits : list bool) : Handler Data :=
    match (deserialize meBits) with
    | None => nop
    | Some (me, rest) =>
      match me with
      | primary => PrimaryInputHandler iBits
      | backup => BackupInputHandler iBits
      end
    end.

  Instance Counter_BaseParams : BaseParams :=
    {
      data := list bool;
      input := list bool;
      output := list bool
    }.

  Definition Nodes : list Name := [primary; backup].

  Lemma all_Names_Nodes : forall n, In n Nodes.
  Proof.
    destruct n; simpl; auto.
  Qed.

  Lemma NoDup_Nodes : NoDup Nodes.
  Proof.
    repeat constructor; simpl; intuition discriminate.
  Qed.

  Instance Counter_MultiParams : MultiParams Counter_BaseParams :=
    {
      name := list bool;
      name_eq_dec := List_eq_dec;
      msg := list bool;
      msg_eq_dec := List_eq_dec;
      nodes := Nodes;
      all_names_nodes := all_Names_Nodes;
      no_dup_nodes := NoDup_Nodes;
      init_handlers := fun _ => serialize init_Data;
      net_handlers := fun dst src msg s =>
                        runGenHandler_ignore s (NetHandler dst msg);
      input_handlers := fun nm i s =>
                        runGenHandler_ignore s (InputHandler nm i)
    }.


  Lemma net_handlers_NetHandler :
    forall h src m d os d' ms,
      net_handlers h src m d = (os, d', ms) ->
      NetHandler h m d = (tt, os, d', ms).
  Proof.
    intros.
    simpl in *.
    monad_unfold.
    repeat break_let.
    find_inversion.
    destruct u. auto.
  Qed.

  Lemma input_handlers_InputHandlers :
    forall h i d os d' ms,
      input_handlers h i d = (os, d', ms) ->
      InputHandler h i d = (tt, os, d', ms).
  Proof.
    intros.
    simpl in *.
    monad_unfold.
    repeat break_let.
    find_inversion.
    destruct u. auto.
  Qed.

  Lemma PrimaryNetHandler_no_msgs :
    forall m d ms d' o u,
      PrimaryNetHandler m d = (u, o, d', ms) ->
      ms = [].
  Proof.
    unfold PrimaryNetHandler.
    intros. monad_unfold.
    break_match; find_inversion; auto.
  Qed.

  Definition inc_in_flight_to_backup (l : list packet) : nat :=
    length (filterMap
              (fun p => if msg_eq_dec (pBody p) inc
                     then if name_eq_dec (pDst p) backup
                          then Some tt else None
                     else None)
              l).

  Lemma inc_in_flight_to_backup_app :
    forall xs ys,
      inc_in_flight_to_backup (xs ++ ys) = inc_in_flight_to_backup xs + inc_in_flight_to_backup ys.
  Proof.
    intros.
    unfold inc_in_flight_to_backup.
    rewrite filterMap_app.
    rewrite app_length.
    auto.
  Qed.

  Lemma inc_in_flight_to_backup_cons_primary_dst :
    forall p,
      pDst p = primary ->
      inc_in_flight_to_backup [p] = 0.
  Proof.
    intros.
    unfold inc_in_flight_to_backup.
    simpl.
    repeat break_match; try congruence; auto.
  Qed.

  Lemma inc_in_flight_to_backup_nil :
    inc_in_flight_to_backup [] = 0.
  Proof.
    reflexivity.
  Qed.

  Lemma InputHandler_inc_in_flight_to_backup_preserved :
    forall h i d u o d' l,
      InputHandler h i d = (u, o, d', l) ->
      d' = d + inc_in_flight_to_backup (send_packets h l).
  Proof.
    unfold InputHandler, PrimaryInputHandler, BackupInputHandler.
    simpl.
    intros.
    monad_unfold.
    repeat break_match; find_inversion; compute; auto.
    rewrite plus_comm. auto.
  Qed.

  Lemma NetHandler_inc_in_flight_to_backup_preserved :
    forall p d u o d' l,
      NetHandler (pDst p) (pBody p) d = (u, o, d', l) ->
      d' + inc_in_flight_to_backup (send_packets (pDst p) l) = d + inc_in_flight_to_backup [p].
  Proof.
    unfold NetHandler, PrimaryNetHandler, BackupNetHandler.
    intros.
    monad_unfold.
    destruct p. simpl in *.
    repeat break_match; find_inversion; simpl; try rewrite inc_in_flight_to_backup_nil;
    unfold Data in *; compute;
    auto with *.
  Qed.

  Lemma InputHandler_backup_no_msgs :
    forall i d u o d' l,
      InputHandler backup i d = (u, o, d', l) ->
      l = [].
  Proof.
    simpl. unfold BackupInputHandler.
    intros.
    monad_unfold.
    find_inversion.
    auto.
  Qed.

  Lemma cons_is_app :
    forall A (x : A) xs,
      x :: xs = [x] ++ xs.
  Proof.
    auto.
  Qed.

  Lemma backup_plus_network_eq_primary :
    forall net tr,
      step_m_star (params := Counter_MultiParams) step_m_init net tr ->
      nwState net backup + inc_in_flight_to_backup (nwPackets net) = nwState net primary.
  Proof.
    intros.
    remember step_m_init as y in *.
    revert Heqy.
    induction H using refl_trans_1n_trace_n1_ind; intros; subst.
    - reflexivity.
    - concludes.
      match goal with
      | [ H : step_m _ _ _ |- _ ] => invc H
      end; simpl.
      + find_apply_lem_hyp net_handlers_NetHandler.
        find_copy_apply_lem_hyp NetHandler_inc_in_flight_to_backup_preserved.
        repeat find_rewrite.
        rewrite cons_is_app in IHrefl_trans_1n_trace1.
        repeat rewrite inc_in_flight_to_backup_app in *.
        destruct (pDst p) eqn:?;
                 try rewrite update_same;
          try rewrite update_diff by congruence;
          unfold send_packets in *; simpl in *.
        * erewrite PrimaryNetHandler_no_msgs with (ms := l) in * by eauto.
          rewrite inc_in_flight_to_backup_cons_primary_dst in * by auto.
          simpl in *. rewrite inc_in_flight_to_backup_nil in *. auto with *.
        * omega.
      + find_apply_lem_hyp input_handlers_InputHandlers.
        find_copy_apply_lem_hyp InputHandler_inc_in_flight_to_backup_preserved.
        unfold send_packets in *. simpl in *.
        rewrite inc_in_flight_to_backup_app. subst.
        destruct h eqn:?;
                 try rewrite update_same;
          try rewrite update_diff by congruence.
        * omega.
        * erewrite InputHandler_backup_no_msgs with (l := l) by eauto.
          simpl. rewrite inc_in_flight_to_backup_nil. omega.
  Qed.

  Theorem primary_ge_backup :
    forall net tr,
      step_m_star (params := Counter_MultiParams) step_m_init net tr ->
      nwState net backup <= nwState net primary.
  Proof.
    intros.
    apply backup_plus_network_eq_primary in H.
    auto with *.
  Qed.

  Definition trace_inputs (tr : list (name * (input + list output))) : nat :=
    length (filterMap (fun e => match e with
                             | (primary, inl i) => Some i
                             | _ => None
                             end) tr).
  Lemma trace_inputs_app :
    forall tr1 tr2,
      trace_inputs (tr1 ++ tr2) = trace_inputs tr1 + trace_inputs tr2.
  Proof.
    unfold trace_inputs.
    intros.
    rewrite filterMap_app.
    rewrite app_length. auto.
  Qed.

  Definition trace_outputs (tr : list (name * (input + list output))) : nat :=
    length (filterMap (fun e => match e with
                             | (primary, inr [o]) => Some o
                             | _ => None
                             end) tr).

  Lemma trace_outputs_app :
    forall tr1 tr2,
      trace_outputs (tr1 ++ tr2) = trace_outputs tr1 + trace_outputs tr2.
  Proof.
    unfold trace_outputs.
    intros.
    rewrite filterMap_app.
    rewrite app_length. auto.
  Qed.

  Definition ack_in_flight_to_primary (l : list packet) : nat :=
    length (filterMap
              (fun p => if msg_eq_dec (pBody p) ack
                     then if name_eq_dec (pDst p) primary
                          then Some tt else None
                     else None)
              l).

  Lemma ack_in_flight_to_primary_app :
    forall xs ys,
      ack_in_flight_to_primary (xs ++ ys) = ack_in_flight_to_primary xs + ack_in_flight_to_primary ys.
  Proof.
    unfold ack_in_flight_to_primary.
    intros.
    rewrite filterMap_app.
    rewrite app_length. auto.
  Qed.

  Lemma ack_in_flight_to_primary_backup :
    forall p,
      pDst p = backup ->
      ack_in_flight_to_primary [p] = 0.
  Proof.
    intros.
    unfold ack_in_flight_to_primary.
    simpl.
    repeat break_match; try congruence; auto.
  Qed.


  Lemma InputHandler_trace_preserved :
    forall h i d u o d' l,
      InputHandler h i d = (u, o, d', l) ->
      trace_inputs [(h, inl i)] =
      trace_outputs [(h, inr o)] +
      inc_in_flight_to_backup (send_packets h l) +
      ack_in_flight_to_primary (send_packets h l).
  Proof.
    unfold InputHandler, PrimaryInputHandler, BackupInputHandler.
    simpl.
    intros.
    monad_unfold.
    repeat break_match; find_inversion; compute; auto.
  Qed.

  Lemma NetHandler_trace_preserved :
    forall p d u o d' l,
      NetHandler (pDst p) (pBody p) d = (u, o, d', l) ->
      inc_in_flight_to_backup [p] +
      ack_in_flight_to_primary [p] =
      trace_outputs [((pDst p), inr o)] +
      inc_in_flight_to_backup (send_packets (pDst p) l) +
      ack_in_flight_to_primary (send_packets (pDst p) l).
  Proof.
    unfold NetHandler, PrimaryNetHandler, BackupNetHandler.
    intros.
    monad_unfold.
    destruct p. simpl in *.
    repeat break_match; find_inversion; simpl; try rewrite inc_in_flight_to_backup_nil;
    unfold Data in *; compute;
    auto with *.
  Qed.

  Lemma trace_inputs_output :
    forall h os,
      trace_inputs [(h, inr os)] = 0.
  Proof.
    intros.
    unfold trace_inputs.
    simpl. repeat break_match; simpl; congruence.
  Qed.

  Lemma trace_outputs_input :
    forall h i,
      trace_outputs [(h, inl i)] = 0.
  Proof.
    intros.
    unfold trace_outputs.
    simpl. repeat break_match; simpl; congruence.
  Qed.

  Lemma trace_outputs_backup :
    forall e,
      trace_outputs [(backup, e)] = 0.
  Proof.
    auto.
  Qed.

  Lemma inputs_eq_outputs_plus_inc_plus_ack :
    forall net tr,
      step_m_star (params := Counter_MultiParams) step_m_init net tr ->
      trace_inputs tr = trace_outputs tr +
                        inc_in_flight_to_backup (nwPackets net) +
                        ack_in_flight_to_primary (nwPackets net).
  Proof.
    intros.
    remember step_m_init as y in *.
    revert Heqy.
    induction H using refl_trans_1n_trace_n1_ind; intros; subst.
    - reflexivity.
    - concludes.
      match goal with
      | [ H : step_m _ _ _ |- _ ] => invc H
      end; simpl.
      + find_apply_lem_hyp net_handlers_NetHandler.
        repeat find_rewrite.
        rewrite trace_inputs_app.
        rewrite trace_outputs_app.
        rewrite cons_is_app with (x := p) in *.
        repeat rewrite inc_in_flight_to_backup_app in *.
        repeat rewrite ack_in_flight_to_primary_app in *.
        find_apply_lem_hyp NetHandler_trace_preserved.
        destruct (pDst p) eqn:?.
        * erewrite inc_in_flight_to_backup_cons_primary_dst in * by eauto.
          rewrite trace_inputs_output in *. simpl in  *. omega.
        * rewrite ack_in_flight_to_primary_backup in * by auto.
          rewrite trace_outputs_backup in *. unfold send_packets in *.
          simpl in *. rewrite <- plus_n_O in *. omega.
      + find_apply_lem_hyp input_handlers_InputHandlers.
        find_apply_lem_hyp InputHandler_trace_preserved.
        rewrite cons_is_app.
        repeat rewrite trace_inputs_app.
        repeat rewrite trace_outputs_app.
        repeat rewrite inc_in_flight_to_backup_app in *.
        repeat rewrite ack_in_flight_to_primary_app in *.
        rewrite trace_outputs_input.
        rewrite trace_inputs_output.
        unfold send_packets in *. simpl in *. omega.
  Qed.

  Theorem inputs_ge_outputs :
    forall net tr,
      step_m_star (params := Counter_MultiParams) step_m_init net tr ->
      trace_outputs tr <= trace_inputs tr.
  Proof.
    intros.
    apply inputs_eq_outputs_plus_inc_plus_ack in H.
    omega.
  Qed.
End Counter.
