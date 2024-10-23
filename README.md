# Full version of the paper for PSSV-2024
Report with description of our approach https://github.com/ivchernenko/PSSV2024-report/blob/main/Chernrnko_PSSV2024_report.pdf

Basic and derived requirement and extra invariant patterns and corresponding lemmas are defined in the following files:
[Pattern1](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern1_Def.thy), [Pattern2](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern2_Def.thy), [Pattern3](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern3_Def.thy), [Pattern4](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern4_Def.thy), [Pattern5](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern5_Def.thy), [Pattern6](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern6_Def.thy), [Pattern7](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern7_Def.thy), [Pattern8](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern8_Def.thy), [Pattern9](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern9_def.thy), [Pattern10](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern10_Def.thy), [Pattern11](https://github.com/ivchernenko/PSSV2024-report/blob/main/Pattern11_Def.thy)

The approach is demonstrated by the vending machine control program.
- poST-program [VendingMachine.post](https://github.com/ivchernenko/PSSV2024-report/blob/main/VendingMachine/VendingMachine.post)
- Verification conditions [VendingMachine.thy](https://github.com/ivchernenko/PSSV2024-report/blob/main/VendingMachine/VendingMachine.thy)
- Requirements in Isabelle/HOL [Requirements.thy](https://github.com/ivchernenko/PSSV2024-report/blob/main/VendingMachine/Requirements.thy)
- Requirement-independent extra invariant [CommonExtraInv.thy](https://github.com/ivchernenko/PSSV2024-report/blob/main/VendingMachine/CommonExtraInv.thy)
- Requirement-dependent extra invariant for requirement Ri is defined in the file ExtraInv_Ri.ty in the directory VendingMachine
- Proofs of verification conditions for requirement Ri and the corresponding extra invariant are in the file Proofs_Ri.thy in the directory VendingMachine
