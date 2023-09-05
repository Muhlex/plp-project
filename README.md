# <p align="center">PLP - Final Project</p>
## <p align="center">A Monte Carlo System for Probabilistic Logic Programming</p>

Sampling of probablistic logic programs for SWI-Prolog, similar to Fabrizio Riguzzi's MCINTYRE (2013):
http://mcs.unife.it/~friguzzi/Papers/Rig13-FI-IJ.pdf


For information regarding approximate inference via Gibbs sampling / Markov Chain Monte Carlo (MCMC) sampling, see [An Analysis of Gibbs Sampling for Probabilistic
Logic Programs](https://ceur-ws.org/Vol-2678/paper12.pdf) or [A Comparison of MCMC Sampling
for Probabilistic Logic Programming
](https://link.springer.com/chapter/10.1007/978-3-030-35166-3_2) (p. 19-29).

Further documentation: https://lukasrieger.github.io/plp-project/

### Running the sampler

1. Start a SWI-Prolog session at the command line via `swipl`
2. Load the `montecarlo` module, e. g. via `[montecarlo].`
3. Invoke `montecarlo('input.pl', Query, P).`, where the first parameter denotes the path to a PLP object program
and the second denotes the query to be sampled. After successful sampling, `P` will contain the sampled probability
of `Query` being true under the given input.

### Available entry points

There are multiple ways to start a sampling process, depending on how much customization of the sampling process is required. 

The `montecarlo` module exposes 3 clauses for this purpose:

- `montecarlo/3` with `montecarlo(Program, Query, Probability)`
- `montecarlo/4` with `montecarlo(Program, Query, Threshold, Probability)`
- `montecarlo/5` with `montecarlo(Program, Query, Threshold, BatchSize, Probability)`

If not specified, Threshold defaults to `0.02` and BatchSize defaults to `500`.

<!--- TODO: Figure out & explain what the threshold means. --->
