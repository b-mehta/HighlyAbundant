# Highly abundant numbers and LCMs

This repository contains formalisations relating to
[this MathOverflow question](https://mathoverflow.net/q/501066/117945), which asks whether or not
every natural `L_n = lcm(1, 2, ..., n)` is highly abundant. A natural is highly abundant if its
sum of divisors is strictly greater than that of any smaller natural.

This was answered in the negative, with the smallest counterexample being `n = 71`.
In fact, it is now known that `L_n` is highly abundant if and only if `n` lies in one of the
intervals `{1, ..., 70}, {81, ..., 96}, {125, ..., 148}, {169, ..., 172}`.

Currently, we formally verify:
- `L_n` is not highly abundant for `71 ≤ n ≤ 80`, `97 ≤ n ≤ 124`, `149 ≤ n ≤ 168` and `173 ≤ n ≤ 100000`.

Work in progress are formal verifications of the following:
- `L_n` is not highly abundant for `173 ≤ n ≤ 10^10`.
- `L_n` is highly abundant for `n` in these intervals `{1, ..., 70}, {81, ..., 96}, {125, ..., 148}, {169, ..., 172}`.
- Assuming the prime number theorem, `L_n` is highly abundant only finitely often.
- Assuming [an effective version of the prime number theorem by Dusart](https://piyanit.nl/wp-content/uploads/2020/10/art_10.1007_s11139-016-9839-4.pdf), `L_n` is not highly abundant for `n ≥ 9 * 10^9`.



<!-- ## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file. -->
