(*
 * © 2021 Massachusetts Institute of Technology.
 * MIT Proprietary, Subject to FAR52.227-11 Patent Rights - Ownership by the Contractor (May 2014)
 * SPDX-License-Identifier: MIT
 * 
 *)

From SPICY Require Import
     ModelCheck.SilentStepElimination
.

From protocols Require Import
     Verification.ShareSecretProtocolSymmetricEncSecure2
     Verification.PGPSecure2
     Verification.SecureDNSSecure2
     Verification.AvgSalarySecure2
     Verification.NetAuthSecure2
.

Set Implicit Arguments.

Module ShareSecretCorrect := SSProtocolSimulates (ShareSecretProtocolSecureSS).
Print Assumptions ShareSecretCorrect.protocol_with_adversary_could_generate_spec.

Module PGPCorrect := SSProtocolSimulates (PGPProtocolSecure).
Print Assumptions PGPCorrect.protocol_with_adversary_could_generate_spec.

Module SecureDNSCorrect := SSProtocolSimulates (SecureDNSProtocolSecure).
Print Assumptions SecureDNSCorrect.protocol_with_adversary_could_generate_spec.

Module AvgSalaryCorrect := SSProtocolSimulates (AvgSalaryProtocolSecure).
Print Assumptions AvgSalaryCorrect.protocol_with_adversary_could_generate_spec.

Module NetAuthCorrect := SSProtocolSimulates (NetAuthProtocolSecure).
Print Assumptions NetAuthCorrect.protocol_with_adversary_could_generate_spec.
