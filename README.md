# Highly abundant numbers and LCMs

This repository contains formalisations relating to
[this MathOverflow question](https://mathoverflow.net/q/501066/117945), which asks whether or not
every natural `L_n = lcm(1, 2, ..., n)` is highly abundant. A natural is highly abundant if its
sum of divisors is strictly greater than that of any smaller natural.

This was answered in the negative, with the smallest counterexample being `n = 71`.
In fact, it is now known that `L_n` is highly abundant if and only if `n` lies in one of the
intervals `{1, ..., 70}, {81, ..., 96}, {125, ..., 148}, {169, ..., 172}`.

Currently, we formally verify:
- `L_n` is not highly abundant for `71 ≤ n ≤ 80`, `97 ≤ n ≤ 124`, `149 ≤ n ≤ 168` and `173 ≤ n ≤ 10^10`. These results can be found in `HighlyAbundant/ClimbLadder.lean`.

Work in progress are formal verifications of the following:
- `L_n` is highly abundant for `n` in these intervals `{1, ..., 70}, {81, ..., 96}, {125, ..., 148}, {169, ..., 172}`.
- `L_n` is not highly abundant for `10^10 ≤ n ≤ 10^40`.
- Assuming the prime number theorem, `L_n` is highly abundant only finitely often.
- Assuming [an effective version of the prime number theorem by Dusart](https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf), `L_n` is not highly abundant for `n ≥ 9 * 10^9`.

## Verifying the formalisation
This proof has been formalised in the Lean theorem prover. To confirm the correctness and completeness yourself, follow these steps.

1. Make sure you have [installed Lean](https://lean-lang.org/install/).
2. Download the repository using `git clone https://github.com/b-mehta/HighlyAbundant.git`.
3. Open the directory where you downloaded the repository (but not any further sub-directory). Open a terminal in this directory and run lake exe cache get! to download built dependencies.
4. In the terminal from step 3, run `lake build` to build this repository. When the process is complete, there will be no output. This shows the proof is correct. Had the build failed or the output included sorryAx, this would have indicated an error or an incomplete proof.


<!-- ## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file. -->
