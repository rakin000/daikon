package daikon.inv.binary.twoScalar;

import daikon.*;
import daikon.inv.*;
import daikon.inv.binary.twoScalar.*;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.checkerframework.checker.interning.qual.Interned;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import typequals.prototype.qual.NonPrototype;
import typequals.prototype.qual.Prototype;

/**
 * Represents an invariant that two double scalars are statistically correlated (Pearson |r| >=
 * threshold). Prints as {@code |corr(x, y)| >= 0.80}.
 */
public final class FloatStatisticallyCorrelated extends TwoFloat {

  static final long serialVersionUID = 20240408L;

  /** Boolean. True iff FloatStatisticallyCorrelated invariants should be considered. */
  public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

  public static final Logger debug =
      Logger.getLogger("daikon.inv.binary.twoScalar.FloatStatisticallyCorrelated");

  /** Minimum absolute Pearson r to consider the variables correlated. */
  static final double CORRELATION_THRESHOLD = 0.90;

  /** Minimum number of samples required before we can report the invariant. */
  static final int MIN_SAMPLES = 10;
  static final double RATIO_THRESHOLD = 1e-4; 
  // Running sums for Pearson r computation
  private long n = 0;
  private double sum_x = 0.0;
  private double sum_y = 0.0;
  private double sum_xx = 0.0;
  private double sum_yy = 0.0;
  private double sum_xy = 0.0;
  private double sum_sq_x_minus_y = 0.0 ; 
  private double abs_max_x_minus_y = Double.MIN_VALUE ;
  // Once falsified, stay falsified
  private boolean falsified = false;

  FloatStatisticallyCorrelated(PptSlice ppt) {
    super(ppt);
  }

  @Prototype FloatStatisticallyCorrelated() {
    super();
  }

  private static @Prototype FloatStatisticallyCorrelated proto =
      new @Prototype FloatStatisticallyCorrelated();

  /** Returns the prototype invariant for FloatStatisticallyCorrelated. */
  public static @Prototype FloatStatisticallyCorrelated get_proto() {
    return proto;
  }

  /** Look up a previously instantiated FloatStatisticallyCorrelated at the given slice. */
  public static @Nullable FloatStatisticallyCorrelated find(PptSlice ppt) {
    assert ppt.arity() == 2;
    for (Invariant inv : ppt.invs) {
      if (inv instanceof FloatStatisticallyCorrelated) {
        return (FloatStatisticallyCorrelated) inv;
      }
    }
    return null;
  }

  @Override
  public boolean enabled() {
    return dkconfig_enabled;
  }

  @Override
  public boolean instantiate_ok(VarInfo[] vis) {
    return valid_types(vis);
  }

  @Override
  protected FloatStatisticallyCorrelated instantiate_dyn(
      @Prototype FloatStatisticallyCorrelated this, PptSlice slice) {
    return new FloatStatisticallyCorrelated(slice);
  }

  @Override
  protected Invariant resurrect_done_swapped() {
    // symmetric — swapping variables doesn't change |r|
    return this;
  }

  @Pure
  @Override
  public boolean is_symmetric() {
    return true;
  }

  @Override
  public String repr(@GuardSatisfied FloatStatisticallyCorrelated this) {
    return "FloatStatisticallyCorrelated" + varNames() + ": r=" + currentR();
  }

  @SideEffectFree
  @Override
  public String format_using(
      @GuardSatisfied FloatStatisticallyCorrelated this, OutputFormat format) {
    String var1name = var1().name_using(format);
    String var2name = var2().name_using(format);

    if (format == OutputFormat.DAIKON) {
      return "|corr(" + var1name + ", " + var2name + ")| >= " + CORRELATION_THRESHOLD + " with ratio " + currentRatio() + " and abs max diff " + abs_max_x_minus_y;
    }

    if (format == OutputFormat.SIMPLIFY) {
      return "(STATISTICALLY_CORRELATED " + var1name + " " + var2name + ")";
    }

    return format_unimplemented(format);
  }

  /** Computes the current Pearson r from running accumulators. Returns NaN if undefined. */
  private double currentR() {
    if (n < 2) {
      return Double.NaN;
    }
    double num = n * sum_xy - sum_x * sum_y;
    double den = Math.sqrt((n * sum_xx - sum_x * sum_x) * (n * sum_yy - sum_y * sum_y));
    if (den == 0.0) {
      return Double.NaN;
    }
    return num / den;
  }

  private double currentRatio() {
    if (n == 0) {
      return Double.NaN;
    }
    return 2.0 * sum_sq_x_minus_y / (sum_xx + sum_yy);
  }

  @Override
  public InvariantStatus check_modified(double v1, double v2, int count) {
    // Individual sample check is not meaningful for a global statistic;
    // falsification happens in add_modified after accumulating enough data.
    return InvariantStatus.NO_CHANGE;
  }

  @Override
  public InvariantStatus add_modified(double v1, double v2, int count) {
    if (falsified) {
      return InvariantStatus.FALSIFIED;
    }

    if (Double.isNaN(v1) || Double.isInfinite(v1) || Double.isNaN(v2) || Double.isInfinite(v2)) {
      return InvariantStatus.NO_CHANGE;
    }

    n += count;
    sum_x += v1 * count;
    sum_y += v2 * count;
    sum_xx += v1 * v1 * count;
    sum_yy += v2 * v2 * count;
    sum_xy += v1 * v2 * count;
    sum_sq_x_minus_y += (v1 - v2) * (v1 - v2) * count;
    abs_max_x_minus_y = Math.max(abs_max_x_minus_y, Math.abs(v1 - v2));
    if (n >= MIN_SAMPLES) {
      double pearson_r = currentR();
      double ratio = currentRatio();
      if (!Double.isNaN(pearson_r) && Math.abs(pearson_r) < CORRELATION_THRESHOLD) {
        falsified = true;
        return InvariantStatus.FALSIFIED;
      }
      // if (!Double.isNaN(ratio) && ratio > RATIO_THRESHOLD) {
      //   falsified = true;
      //   return InvariantStatus.FALSIFIED;
      // }
    }

    return InvariantStatus.NO_CHANGE;
  }

  @Override
  protected double computeConfidence() {
    if (n < MIN_SAMPLES) {
      return Invariant.CONFIDENCE_UNJUSTIFIED;
    }
    double r = currentR();
    if (Double.isNaN(r)) {
      return Invariant.CONFIDENCE_UNJUSTIFIED;
    }
    // Map |r| in [threshold, 1] → [0, CONFIDENCE_JUSTIFIED]
    double absR = Math.abs(r);
    if (absR < CORRELATION_THRESHOLD) {
      return Invariant.CONFIDENCE_UNJUSTIFIED;
    }
    double ratio = currentRatio() ; 
    if (Double.isNaN(ratio) || ratio > RATIO_THRESHOLD) {
      return Invariant.CONFIDENCE_UNJUSTIFIED;
    }
    return Invariant.CONFIDENCE_JUSTIFIED;
  }

  @Override
  public boolean enoughSamples(@GuardSatisfied FloatStatisticallyCorrelated this) {
    return n >= MIN_SAMPLES;
  }

  @Override
  public @Nullable FloatStatisticallyCorrelated merge(List<Invariant> invs, PptSlice parent_ppt) {
    FloatStatisticallyCorrelated first = (FloatStatisticallyCorrelated) invs.get(0);
    FloatStatisticallyCorrelated result = (FloatStatisticallyCorrelated) first.clone();
    result.ppt = parent_ppt;
    for (int i = 1; i < invs.size(); i++) {
      FloatStatisticallyCorrelated child = (FloatStatisticallyCorrelated) invs.get(i);
      result.n += child.n;
      result.sum_x += child.sum_x;
      result.sum_y += child.sum_y;
      result.sum_xx += child.sum_xx;
      result.sum_yy += child.sum_yy;
      result.sum_xy += child.sum_xy;
      result.sum_sq_x_minus_y += child.sum_sq_x_minus_y;  
      result.abs_max_x_minus_y = Math.max(result.abs_max_x_minus_y, child.abs_max_x_minus_y); 
      if (child.falsified) {
        result.falsified = true;
      }
    }
    result.log("Merged '%s' from %s child invariants", result.format(), invs.size());
    return result;
  }

  @Pure
  @Override
  public boolean isSameFormula(Invariant other) { 
    return true; // other instanceof FloatStatisticallyCorrelated;
  }

  /**
   * Statistical correlation is mutually exclusive with exact relational and linear invariants: if a
   * deterministic ordering, equality, or linear-equation relationship already holds between the two
   * variables, reporting a probabilistic correlation is either subsumed (linear equation implies
   * |r|=1) or contradictory in intent (non-equality / strict ordering tells us nothing about
   * co-variation). Daikon will therefore never print both this invariant and any of the listed
   * classes for the same variable pair.
   */
  @Pure
  @Override
  public boolean isExclusiveFormula(Invariant other) {
    // Only exact equality and linear equations are truly exclusive with statistical correlation:
    // both imply |r| = 1, making the weaker invariant redundant. Ordering invariants (< > <= >=)
    // and non-equality can coexist with correlation and are not exclusive.
    return (other instanceof FloatEqual)
        || (other instanceof LinearBinaryFloat)
        || (other instanceof LinearBinary);
  }

  /**
   * Suppress this invariant when a stronger deterministic relationship between the two variables
   * is already established at this program point: exact equality or a linear equation both imply
   * |r| = 1 and therefore subsume a probabilistic correlation. Ordering invariants (< > <= >=)
   * do not subsume correlation and are left to coexist.
   */
  @Pure
  @Override
  public @Nullable DiscardInfo isObviousDynamically(VarInfo[] vis) {
    DiscardInfo super_result = super.isObviousDynamically(vis);
    if (super_result != null) {
      return super_result;
    }

    PptSlice pptSlice = ppt;

    if (FloatEqual.find(pptSlice) != null) {
      return new DiscardInfo(this, DiscardCode.obvious,
          "x == y implies perfect correlation");
    }
    if (LinearBinaryFloat.find(pptSlice) != null) {
      return new DiscardInfo(this, DiscardCode.obvious,
          "linear equation y=ax+b implies |r|=1, subsuming statistical correlation");
    }

    return null;
  }

  @Override
  public InvariantStatus add(
      @Interned Object v1, @Interned Object v2, int mod_index, int count) {
    if (debug.isLoggable(Level.FINE)) {
      debug.fine(
          "FloatStatisticallyCorrelated"
              + ppt.varNames()
              + ".add("
              + v1
              + ","
              + v2
              + ", mod_index="
              + mod_index
              + "), count="
              + count
              + ")");
    }
    return super.add(v1, v2, mod_index, count);
  }
}
