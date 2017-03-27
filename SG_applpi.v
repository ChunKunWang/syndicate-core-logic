Add LoadPath "/home/amos/applpi".
(** https://github.com/syndicate-storage/syndicate-core/blob/master/protobufs/sg.proto *)

Require Import libapplpi.
Require Import SG_applpi_string.
Require Import SG_fs.
Require Import Coq.FSets.FMapList.
Require Import Coq.Strings.String.

(** Result channel *)
Axiom result_chan : chan unit false.
Definition succ : proc := OutAtom result_chan tt.

(** Catch IO exception *)
Axiom IOexn_chan : chan unit false.
Definition IOexn := OutAtom IOexn_chan tt.

(** Catch a system failure *)
Axiom system_failure_chan : chan unit false.
Definition failure := OutAtom system_failure_chan tt.

Definition may_fail := nuP
  (fun x => parP (InAtom x)
    (parP (OutAtom x tt) (x ?? (fun _ => OutAtom system_failure_chan tt)))).

(** Manifest data plane *)
(* c.f. protobufs/sg.proto: l.44-60 *)
Record Manifest : Set := manifest
  { volume_id : string;
    owner_id : string;
    file_id : string;
    size : string}.

(** Definition of Syndicate requests from client *)
(* c.f. protobufs/sg.proto: l.80-94 *)
Inductive SG_req : Set :=
  | req_write : string -> SG_req
  | req_truncate: string -> SG_req
  | req_detach: string -> SG_req
  | req_rename: string -> SG_req
  | req_putchunks: string -> SG_req
  | req_deletechunks: string -> SG_req
  | req_setxattr: string -> SG_req
  | req_removexattr: string -> SG_req
  | req_reload: string -> SG_req
  | req_refresh: string -> SG_req
  | req_rename_hint: string -> SG_req.

Record md_HTTP_connection_data : Set := con_data
  { header_message : SG_req}.

Definition InputStream : Set := chan SG_req true.

(** Response messages *)
Inductive RespMsg : Set :=
  | resp_write : RespMsg
  | resp_truncate : RespMsg
  | resp_detach : RespMsg
  | resp_rename : RespMsg
  | resp_putchunks : RespMsg
  | resp_deletechunks : RespMsg
  | resp_setxattr : RespMsg
  | resp_removexattr : RespMsg
  | resp_reload : RespMsg
  | resp_refresh : RespMsg
  | resp_rename_hint : RespMsg.

Definition OutputStream := chan RespMsg true.

Record SGstate : Set := sg_state
  {in_stream : InputStream;
   to_client : OutputStream;
(* Manifest info *)
   from_client : Manifest;
(* file system is modeled as a process *)
   to_fs : FileSystemState }.

Definition update_from (st : SGstate) (data: Manifest) : SGstate := 
  sg_state (in_stream st) (to_client st)
  data (to_fs st).

Definition STATE : Set := SGstate.

Definition reply (r : RespMsg) (c : OutputStream) (cont : proc) : proc :=
  c << r >> cont.

Definition get_req (c : InputStream) (cont : SG_req -> proc) : proc :=
  c ?? cont.

(* a -> b -> c => a * b -> c*)

Definition sample_server (i:chan (nat * (chan nat true)) false) : proc := 
    rinP i (fun ar => let a := fst ar in let r := snd ar in OutAtom r (plus a 1)).

Definition sample_client (i:chan (nat * (chan nat true)) false) (o:chan nat true) : proc :=
    nuPl (fun r => parP (OutAtom i (0,r)) (inP r (fun x => OutAtom o x))).

Definition sample_Run (i : chan (nat * (chan nat true)) false) (o : chan nat true) := 
  (parP (sample_server i) (sample_client i o)).


Definition server (i:chan (md_HTTP_connection_data * (chan nat true)) false) : proc := 
    rinP i (fun ar => let a := fst ar in let r := snd ar in OutAtom r O).

Definition client (req : md_HTTP_connection_data) (i:chan (md_HTTP_connection_data * (chan nat true)) false) (o:chan nat true) : proc :=
    nuPl (fun r => parP (OutAtom i (req,r)) (inP r (fun x => OutAtom o x))).

Definition Run (req : md_HTTP_connection_data) (i : chan (md_HTTP_connection_data * (chan nat true)) false) (o : chan nat true) := 
  (parP (server i) (client req i o)).


