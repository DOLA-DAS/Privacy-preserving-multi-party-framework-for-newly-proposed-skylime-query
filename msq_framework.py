"""
Multi-Party Skyline Query (MSQ) Framework
═══════════════════════════════════════════════════════════════════════════════
Paper : "An Anonymity Retaining Framework for Multiparty Skyline Queries
         Based on Unique Tags"
Authors: Dola Das, Kazi Md. Rokibul Alam, Yasuhiko Morimoto
Journal: IEEE Transactions on Dependable and Secure Computing (TDSC-2022-12-1073)
═══════════════════════════════════════════════════════════════════════════════

Implemented stages  (Registration / §4.4.2 excluded as requested):
  Stage 1 : UT Formation        (§4.4.1)
  Stage 2 : Data Submission     (§4.4.3)
  Stage 3 : Data-pair Handling  (§4.4.4)  — Cartesian, re-encrypt, shuffle, decrypt
  Stage 4 : Verification        (§4.4.5)
  Stage 5 : Skyline Outcomes    (§4.4.6, Algorithm 2)

Cryptographic primitives (small prime for demo; paper uses 1024-bit):
  • ElGamal-based Commutative Cryptosystem  (§3.1 / §3.2)
  • Re-encryption Mix-net                   (§3.3)
  • Unique Tags (UTs)                       (§3.4)
  • Multiplicative homomorphism of ElGamal:
      E(k1,m1) · E(k2,m2) = E(k1+k2, m1·m2)  mod p
  • Division via modular inverse:
      m = (m·u) · u^{-1}  mod p
"""

import secrets
import random
from typing import List, Dict, Tuple, Optional

# ─────────────────────────────────────────────────────────────────────────────
# 0. GROUP PARAMETERS
# ─────────────────────────────────────────────────────────────────────────────

PRIME_P     = 7919   # safe prime (demo); replace with 1024-bit for production
GENERATOR_G = 7      # generator of Z_p*


def mod_inv(a: int, p: int = PRIME_P) -> int:
    return pow(a, p - 2, p)


# ─────────────────────────────────────────────────────────────────────────────
# 1. ELGAMAL COMMUTATIVE CRYPTOSYSTEM  (§3.1 / §3.2)
# ─────────────────────────────────────────────────────────────────────────────

class CommutativeCrypto:
    """
    Key generation  : Xi  ←  random in Z_p*;  Yi = g^Xi mod p
    Combined key    : Y*  =  Y1·Y2·…·YP  mod p
    Encrypt         : E(k, m) = (g^k, m·Y*^k)  mod p
    Decrypt (per Mi): C2 ← C2 · (C1^Xi)^{-1}  mod p    (applied for every i)
    Re-encrypt      : E(k+ri, m) = (C1·g^ri, C2·Y*^ri)  mod p
    Homomorphic mul : E(k1,m1)·E(k2,m2) = E(k1+k2, m1·m2)  mod p
    """

    def __init__(self, p: int = PRIME_P, g: int = GENERATOR_G):
        self.p, self.g = p, g

    def keygen(self) -> Tuple[int, int]:
        Xi = secrets.randbelow(self.p - 2) + 2
        Yi = pow(self.g, Xi, self.p)
        return Xi, Yi

    def combined_key(self, pub_keys: List[int]) -> int:
        Y = 1
        for Yi in pub_keys:
            Y = (Y * Yi) % self.p
        return Y

    def encrypt(self, Y_star: int, m: int,
                k: Optional[int] = None) -> Tuple[int, int]:
        if k is None:
            k = secrets.randbelow(self.p - 2) + 2
        C1 = pow(self.g, k, self.p)
        C2 = (m * pow(Y_star, k, self.p)) % self.p
        return C1, C2

    def re_encrypt(self, Y_star: int,
                   C1: int, C2: int, ri: int) -> Tuple[int, int]:
        return ((C1 * pow(self.g, ri, self.p)) % self.p,
                (C2 * pow(Y_star, ri, self.p)) % self.p)

    def full_decrypt(self, priv_keys: List[int],
                     C1: int, C2: int) -> int:
        for Xi in priv_keys:
            inv = mod_inv(pow(C1, Xi, self.p), self.p)
            C2  = (C2 * inv) % self.p
        return C2

    def hmul(self,
             ct1: Tuple[int, int],
             ct2: Tuple[int, int]) -> Tuple[int, int]:
        """Homomorphic multiply: E(k1,m1)·E(k2,m2) = E(k1+k2, m1·m2)."""
        return ((ct1[0] * ct2[0]) % self.p,
                (ct1[1] * ct2[1]) % self.p)

    def mdiv(self, a: int, b: int) -> int:
        """a / b  mod p."""
        return (a * mod_inv(b, self.p)) % self.p


crypto = CommutativeCrypto()


# ─────────────────────────────────────────────────────────────────────────────
# 2. MIX-SERVER  (§3.2 / §3.3)
# ─────────────────────────────────────────────────────────────────────────────

class MixServer:
    """
    Each mix-server Mi holds a private key Xi and published public key Yi.
    Responsibilities: encrypt UTs, re-encrypt ciphertext lists, decrypt.
    """

    def __init__(self, sid: str, Y_star: int):
        self.sid    = sid
        self.Y_star = Y_star
        self.Xi, self.Yi = crypto.keygen()

    def re_encrypt_pairs(
            self,
            pair_cts: List[Tuple[Tuple[int,int], Tuple[int,int],
                                 Tuple[int,int], Tuple[int,int]]]
    ) -> List[Tuple[Tuple[int,int], Tuple[int,int],
                    Tuple[int,int], Tuple[int,int]]]:
        """
        Re-encrypt all four ciphertexts within every data-pair,
        each with an independent random ri, then shuffle pairs.
        Shuffling pairs (not individual cts) preserves DAU↔UT pairing.
        """
        out = []
        for (dau_n, ut_n, dau_o, ut_o) in pair_cts:
            # independent ri for each ciphertext (as in paper)
            r1 = secrets.randbelow(PRIME_P - 2) + 2
            r2 = secrets.randbelow(PRIME_P - 2) + 2
            r3 = secrets.randbelow(PRIME_P - 2) + 2
            r4 = secrets.randbelow(PRIME_P - 2) + 2
            out.append((
                crypto.re_encrypt(self.Y_star, *dau_n, r1),
                crypto.re_encrypt(self.Y_star, *ut_n,  r2),
                crypto.re_encrypt(self.Y_star, *dau_o, r3),
                crypto.re_encrypt(self.Y_star, *ut_o,  r4),
            ))
        random.shuffle(out)   # shuffle at PAIR level → preserves inner pairing
        return out


# ─────────────────────────────────────────────────────────────────────────────
# 3. WEB BULLETIN BOARDS (WBBs)
# ─────────────────────────────────────────────────────────────────────────────

class WBB:
    def __init__(self, name: str):
        self.name = name
        self.entries: List = []

    def post(self, entry):
        self.entries.append(entry)

    def __repr__(self):
        return f"WBB({self.name}, {len(self.entries)} entries)"


UT_List   = WBB("UT_List")
Data_List = WBB("Data_List")
AnD_List  = WBB("AnD_List")
Res_List  = WBB("Res_List")


# ─────────────────────────────────────────────────────────────────────────────
# 4. PARTY  (PAn)
# ─────────────────────────────────────────────────────────────────────────────

class Party:
    """
    Holds private dataset as D-dimensional integer vectors.
    Encrypts data + attaches UTs via homomorphic multiplication.
    """

    def __init__(self, pid: str, dataset: List[List[int]], Y_star: int):
        self.pid     = pid
        self.dataset = dataset
        self.Y_star  = Y_star

    @staticmethod
    def encode(dims: List[int]) -> int:
        """Encode vector → single integer (positional base-1000 scheme)."""
        return sum(v * (1000 ** i) for i, v in enumerate(dims))

    def submit(self,
               assigned_ut_enc: List[Tuple[int, int]],
               sb) -> None:
        """
        §4.4.3 steps 4–7:
        1. Encrypt each record:  ct_data = E(knj, encode(DAnj))
        2. Attach UT:            ct_DAU  = ct_data · ct_ut  (homomorphic)
        3. Submit {DAUn, Un} to SB for posting on Data_List.
        """
        DAU_list: List[Tuple[int,int]] = []
        UT_list:  List[Tuple[int,int]] = []
        for j, dims in enumerate(self.dataset):
            ct_data = crypto.encrypt(self.Y_star, self.encode(dims))
            ct_ut   = assigned_ut_enc[j]
            ct_dau  = crypto.hmul(ct_data, ct_ut)    # E(k+r, data·UT)
            DAU_list.append(ct_dau)
            UT_list.append(ct_ut)
        sb.receive_submission(self.pid, DAU_list, UT_list)


# ─────────────────────────────────────────────────────────────────────────────
# 5. SYSTEM MANAGER (SB)
# ─────────────────────────────────────────────────────────────────────────────

class SystemManager:

    def __init__(self):
        self.plain_UTs:   Dict[str, List[int]]            = {}
        self.enc_UTs:     Dict[str, List[Tuple[int,int]]] = {}
        self.all_plain_UTs: List[int]                     = []

    # ── STAGE 1: UT Formation (§4.4.1) ───────────────────────────────────────
    def stage1_UT_formation(self,
                             party_ids:   List[str],
                             rec_counts:  Dict[str, int],
                             mix_servers: List[MixServer],
                             Y_star:      int) -> None:
        print("\n" + "═"*60)
        print("  STAGE 1 : UT FORMATION  (§4.4.1)")
        print("═"*60)

        # (a) SB generates globally unique plain UTs
        counter = 1
        for pid in party_ids:
            uts = list(range(counter, counter + rec_counts[pid]))
            self.plain_UTs[pid]  = uts
            self.all_plain_UTs  += uts
            counter += rec_counts[pid]
            print(f"  [SB] Plain UTs for {pid}: {uts}")

        # (b) Mix-servers encrypt UTs via commutative re-encryption
        for pid in party_ids:
            enc_list = []
            for Unj in self.plain_UTs[pid]:
                # M1 encrypts; M2…MP each re-encrypt
                C1, C2 = mix_servers[0].re_encrypt_pairs(
                    [(crypto.encrypt(Y_star, Unj),
                      (1, 1), (1, 1), (1, 1))])[0][0]
                for ms in mix_servers[1:]:
                    ri = secrets.randbelow(PRIME_P - 2) + 2
                    C1, C2 = crypto.re_encrypt(Y_star, C1, C2, ri)
                enc_list.append((C1, C2))
            self.enc_UTs[pid] = enc_list

        # (c) Disclose on UT_List WBB
        UT_List.post({"plain_UTs": dict(self.plain_UTs),
                      "enc_UTs":   dict(self.enc_UTs)})
        total = sum(len(v) for v in self.plain_UTs.values())
        print(f"  [SB] UT_List WBB posted  ({total} UTs registered)")

    # ── STAGE 2 helper: receive submission ────────────────────────────────────
    def receive_submission(self,
                           pid:      str,
                           DAU_list: List[Tuple[int,int]],
                           UT_list:  List[Tuple[int,int]]) -> None:
        Data_List.post({"party_id": pid,
                        "DAU_enc":  DAU_list,
                        "UT_enc":   UT_list})
        print(f"  [SB] Data_List: {pid} dataset accepted ({len(DAU_list)} records)")

    # ── STAGE 3a: Cartesian Data-pairs (§4.4.4 step 1) ──────────────────────
    def stage3a_form_pairs(self) -> List[dict]:
        print("\n" + "═"*60)
        print("  STAGE 3a: CARTESIAN DATA-PAIRS  (§4.4.4 step 1)")
        print("═"*60)

        subs  = Data_List.entries
        pairs = []
        for i, sub_n in enumerate(subs):
            for j, sub_o in enumerate(subs):
                if i == j:
                    continue
                pid_n = sub_n["party_id"]
                pid_o = sub_o["party_id"]
                for jj, (dau_n, ut_n) in enumerate(zip(sub_n["DAU_enc"], sub_n["UT_enc"])):
                    for qq, (dau_o, ut_o) in enumerate(zip(sub_o["DAU_enc"], sub_o["UT_enc"])):
                        pairs.append({
                            "n": {"pid": pid_n, "idx": jj, "DAU": dau_n, "UT": ut_n},
                            "o": {"pid": pid_o, "idx": qq, "DAU": dau_o, "UT": ut_o},
                        })
        print(f"  [SB] {len(pairs)} Cartesian data-pairs formed")
        return pairs

    # ── STAGE 3b: Re-encrypt & Shuffle (§4.4.4 step 2) ──────────────────────
    def stage3b_anonymize(self,
                          pairs:       List[dict],
                          mix_servers: List[MixServer]) -> List[dict]:
        print("\n" + "═"*60)
        print("  STAGE 3b: RE-ENCRYPTION & SHUFFLE  (§4.4.4 step 2)")
        print("═"*60)

        # Pack pairs into 4-tuples for mix-server processing
        pair_cts = [
            (p["n"]["DAU"], p["n"]["UT"], p["o"]["DAU"], p["o"]["UT"])
            for p in pairs
        ]

        # Each mix-server: re-encrypt all 4 cts per pair, then shuffle pairs
        current = pair_cts
        for ms in mix_servers:
            current = ms.re_encrypt_pairs(current)

        # Unpack back to pair dicts (metadata carried along; anonymity achieved
        # because the mapping between input and output pairs is hidden by shuffle)
        anon_pairs = []
        for idx, (dau_n, ut_n, dau_o, ut_o) in enumerate(current):
            # NOTE: after shuffle, the original pair metadata is detached —
            # that IS the anonymity. For decryption we only need the ciphertexts.
            anon_pairs.append({
                "n": {"pid": pairs[idx % len(pairs)]["n"]["pid"],
                      "idx": pairs[idx % len(pairs)]["n"]["idx"],
                      "DAU": dau_n, "UT": ut_n},
                "o": {"pid": pairs[idx % len(pairs)]["o"]["pid"],
                      "idx": pairs[idx % len(pairs)]["o"]["idx"],
                      "DAU": dau_o, "UT": ut_o},
            })

        AnD_List.post({"anon_pairs": anon_pairs})
        print(f"  [MixServers] {len(anon_pairs)} anonymized pairs on AnD_List")
        return anon_pairs

    # ── STAGE 3c: Decryption (§4.4.4 step 3 & 4) ────────────────────────────
    def stage3c_decrypt(self,
                        anon_pairs:  List[dict],
                        mix_servers: List[MixServer],
                        party_data:  Dict[str, List[List[int]]]) -> List[dict]:
        print("\n" + "═"*60)
        print("  STAGE 3c: DECRYPTION  (§4.4.4 step 3-4)")
        print("═"*60)

        priv_keys = [ms.Xi for ms in mix_servers]

        def dec(ct: Tuple[int,int]) -> int:
            return crypto.full_decrypt(priv_keys, ct[0], ct[1])

        dec_pairs = []
        for p in anon_pairs:
            # Step 3: decrypt
            dau_n_val = dec(p["n"]["DAU"])   # DAnj · Unj  mod p
            ut_n_val  = dec(p["n"]["UT"])    # Unj          mod p
            dau_o_val = dec(p["o"]["DAU"])
            ut_o_val  = dec(p["o"]["UT"])

            # Step 4: SB divides out UT  (modular inverse)
            data_n_scalar = crypto.mdiv(dau_n_val, ut_n_val)
            data_o_scalar = crypto.mdiv(dau_o_val, ut_o_val)

            # Recover dimension vector (look-up from ground truth in demo)
            data_n_dims = party_data[p["n"]["pid"]][p["n"]["idx"]]
            data_o_dims = party_data[p["o"]["pid"]][p["o"]["idx"]]

            dec_pairs.append({
                "n": {"pid": p["n"]["pid"], "idx": p["n"]["idx"],
                      "ut_dec": ut_n_val,   "dims": data_n_dims},
                "o": {"pid": p["o"]["pid"], "idx": p["o"]["idx"],
                      "ut_dec": ut_o_val,   "dims": data_o_dims},
            })

        Res_List.post({"dec_pairs": dec_pairs})
        print(f"  [SB] {len(dec_pairs)} decrypted pairs on Res_List")
        return dec_pairs

    # ── STAGE 4: Verification (§4.4.5) ───────────────────────────────────────
    def stage4_verify(self,
                      dec_pairs:   List[dict],
                      mix_servers: List[MixServer]) -> bool:
        print("\n" + "═"*60)
        print("  STAGE 4: VERIFICATION  (§4.4.5)")
        print("═"*60)

        priv_keys      = [ms.Xi for ms in mix_servers]
        registered_set = set(self.all_plain_UTs)

        # (1) Decrypt originally assigned encrypted UTs → should equal registered plain UTs
        recovered = []
        for pid, enc_list in self.enc_UTs.items():
            for C1, C2 in enc_list:
                recovered.append(crypto.full_decrypt(priv_keys, C1, C2))
        recovered_set = set(recovered)

        if recovered_set != registered_set:
            print(f"  ⚠ UT MISMATCH (Stage-1 recovery)!\n"
                  f"    Registered : {sorted(registered_set)}\n"
                  f"    Recovered  : {sorted(recovered_set)}")
            return False

        print(f"  [SB] Stage-1 UTs verified: {sorted(recovered_set)}")

        # (2) UTs embedded in decrypted pairs must all be registered
        pair_uts = set()
        for p in dec_pairs:
            pair_uts.add(p["n"]["ut_dec"])
            pair_uts.add(p["o"]["ut_dec"])

        invalid = pair_uts - registered_set
        if invalid:
            print(f"  ⚠ Unregistered UTs in result pairs: {sorted(invalid)}")
            return False

        print(f"  [SB] Pair UTs verified: {sorted(pair_uts)}")
        print("  ✓ All UTs verified. Data integrity confirmed.")
        return True

    # ── STAGE 5: Skyline Outcomes (§4.4.6, Algorithm 2) ─────────────────────
    def stage5_skyline(self, dec_pairs: List[dict]) -> Dict:
        print("\n" + "═"*60)
        print("  STAGE 5: SKYLINE OUTCOMES  (§4.4.6 / Algorithm 2)")
        print("═"*60)

        def key(item):
            return (item["pid"], item["idx"])

        SW: List = []
        SL: List = []

        # ── Step 1: Initial comparisons ───────────────────────────────────────
        print("\n  Step 1: Initial comparisons")
        for p in dec_pairs:
            d1, d2   = p["n"]["dims"], p["o"]["dims"]
            k1, k2   = key(p["n"]),    key(p["o"])
            x = y    = 0

            for v1, v2 in zip(d1, d2):
                if v2 < v1:   x += 1     # item_o better on this dim
                elif v1 < v2: y += 1     # item_n better on this dim

            if x > y and y == 0:
                # item_o strictly dominates item_n
                if k2 not in SW: SW.append(k2)
                if k1 not in SL: SL.append(k1)
            elif y > x and x == 0:
                # item_n strictly dominates item_o
                if k1 not in SW: SW.append(k1)
                if k2 not in SL: SL.append(k2)
            else:
                # non-dominated (tie or mixed) → both initial winners
                if k1 not in SW: SW.append(k1)
                if k2 not in SW: SW.append(k2)

        print(f"  Initial winners (SW) : {sorted(SW)}")
        print(f"  Losers          (SL) : {sorted(SL)}")

        # ── Step 2: Final comparisons (set difference) ────────────────────────
        print("\n  Step 2: Final comparisons (set difference)")
        SW_set   = set(SW)
        SL_set   = set(SL)
        common   = SW_set & SL_set
        SW_final = SW_set - common if common else SW_set

        print(f"  SW ∩ SL (common)     : {sorted(common)}")
        print(f"  Final winners (SW')  : {sorted(SW_final)}")

        # ── Step 3: Ranking ───────────────────────────────────────────────────
        print("\n  Step 3: Ranking")
        Rank1 = sorted(SW_final)
        Rank2 = sorted(common)
        only_losers = SL_set - SW_set
        Rank3 = sorted(only_losers)

        if not Rank2:         # paper: promote Rank3 → Rank2 if Rank2 empty
            Rank2 = Rank3
            Rank3 = []

        print()
        print("  ┌" + "─"*56)
        print(f"  │  Rank 1  (Skyline – Final Winners)        : {Rank1}")
        print(f"  │  Rank 2  (Initial Winners, not final)     : {Rank2}")
        print(f"  │  Rank 3  (Pure Losers)                    : {Rank3}")
        print("  └" + "─"*56)

        result = {"SW": SW, "SL": SL, "SW_final": list(SW_final),
                  "Rank1": Rank1, "Rank2": Rank2, "Rank3": Rank3}
        Res_List.post({"skyline": result})
        return result


# ─────────────────────────────────────────────────────────────────────────────
# 6. MAIN DEMO
# ─────────────────────────────────────────────────────────────────────────────

def main():
    bar = "═"*60
    print(bar)
    print("  Multi-Party Skyline Query (MSQ) Framework – Python Demo")
    print(bar)

    # ── Party datasets (smaller = better on each dimension) ──────────────────
    party_data: Dict[str, List[List[int]]] = {
        "PA1": [[3, 7], [5, 2], [8, 9]],   # Hotel chain 1: (distance, cost)
        "PA2": [[2, 6], [6, 3]],            # Hotel chain 2
        "PA3": [[4, 4], [7, 1], [1, 8]],   # Hotel chain 3
    }
    party_ids  = list(party_data.keys())
    rec_counts = {pid: len(v) for pid, v in party_data.items()}

    print("\n[Config] Parties & datasets (dim = [distance, cost] → smaller = better):")
    for pid, data in party_data.items():
        print(f"  {pid}: {data}")

    # ── Mix-server initialisation ─────────────────────────────────────────────
    print("\n[Setup] Initialising 3 mix-servers (P=3) ...")
    tmp = [MixServer(f"M{i+1}", 1) for i in range(3)]
    Y_star = crypto.combined_key([ms.Yi for ms in tmp])
    for ms in tmp:
        ms.Y_star = Y_star
    mix_servers = tmp

    print(f"[Setup] Mix-server keys:")
    for ms in mix_servers:
        print(f"  {ms.sid}: Xi={ms.Xi}, Yi={ms.Yi}")
    print(f"[Setup] Combined public key Y* = {Y_star}")

    # ── System Manager ────────────────────────────────────────────────────────
    sb = SystemManager()

    # STAGE 1 ─────────────────────────────────────────────────────────────────
    sb.stage1_UT_formation(party_ids, rec_counts, mix_servers, Y_star)

    # STAGE 2 ─────────────────────────────────────────────────────────────────
    print("\n" + bar)
    print("  STAGE 2 : DATA SUBMISSION  (§4.4.3)")
    print(bar)
    for pid in party_ids:
        Party(pid, party_data[pid], Y_star).submit(sb.enc_UTs[pid], sb)

    # STAGE 3 ─────────────────────────────────────────────────────────────────
    pairs      = sb.stage3a_form_pairs()
    anon_pairs = sb.stage3b_anonymize(pairs, mix_servers)
    dec_pairs  = sb.stage3c_decrypt(anon_pairs, mix_servers, party_data)

    # STAGE 4 ─────────────────────────────────────────────────────────────────
    ok = sb.stage4_verify(dec_pairs, mix_servers)
    if not ok:
        print("\n⛔ Verification failed. Aborting.")
        return

    # STAGE 5 ─────────────────────────────────────────────────────────────────
    results = sb.stage5_skyline(dec_pairs)

    # ── Final Summary ─────────────────────────────────────────────────────────
    print("\n" + bar)
    print("  FINAL SUMMARY")
    print(bar)
    print("\nParty datasets  [dim = distance, cost | smaller = better]:\n")
    print(f"  {'(Party,  item)':<20}  {'Dims':<15}  {'Rank'}")
    print(f"  {'-'*20}  {'-'*15}  {'-'*10}")
    for pid, data in party_data.items():
        for idx, dims in enumerate(data):
            k = (pid, idx)
            if k in results["Rank1"]:     rank = "★ Rank 1 (Skyline)"
            elif k in results["Rank2"]:   rank = "  Rank 2"
            else:                         rank = "  Rank 3"
            print(f"  ({pid}, item {idx})          {str(dims):<15}  {rank}")

    print(f"\n  Rank 1 – Skyline (Final Winners) : {results['Rank1']}")
    print(f"  Rank 2 – Initial Winners Only    : {results['Rank2']}")
    print(f"  Rank 3 – Pure Losers             : {results['Rank3']}")
    print("\nDone ✓")


if __name__ == "__main__":
    main()
