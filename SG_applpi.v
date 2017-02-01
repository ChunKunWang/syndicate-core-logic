Add LoadPath "/home/amos/applpi".

Require Import libapplpi.
Require Import SG_applpi_string.

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
  { volume_id : String; 
    coordinator_id : String;
    owner_id : String;
    file_id : String;
    file_version : String;
    size : String}.

(** Definition of Syndicate requests from client *)
(* c.f. protobufs/sg.proto: l.80-94 *)
Inductive SG_req : Set :=
  | req_write : String -> SG_req
  | req_truncate: String -> SG_req
  | req_detach: String -> SG_req
  | req_rename: String -> SG_req
  | req_putchunks: String -> SG_req
  | req_deletechunks: String -> SG_req
  | req_setxattr: String -> SG_req
  | req_removexattr: String -> SG_req
  | req_reload: String -> SG_req
  | req_refresh: String -> SG_req
  | req_rename_hint: String -> SG_req.

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
