package daikon.inv.unary.scalar;

import daikon.PptSlice;
import daikon.inv.Invariant;
import daikon.inv.InvariantStatus;
import daikon.inv.OutputFormat;
import java.util.List;
import java.util.logging.Logger;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import typequals.prototype.qual.Prototype;

/**
 * Learns a Gaussian model (mean, standard deviation) of a double scalar from an initial "learning"
 * window of samples, then freezes those parameters and uses them to flag later samples as
 * out-of-distribution (OOD) at runtime via a z-score test. Prints as {@code x ~ N(mean, stddev)}
 * while all samples fit, and is falsified as soon as an OOD sample is observed after learning.
 */
public final class OutOfDistributionFloat extends SingleFloat {

  static final long serialVersionUID = 20260903L;

  /** Boolean. True iff OutOfDistributionFloat invariants should be considered. */
  public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

  /** Number of samples used to learn the distribution before runtime OOD detection begins. */
  public static int dkconfig_learning_samples = 30;

  /** Number of standard deviations from the learned mean that counts as out-of-distribution. */
  public static double dkconfig_z_threshold = 4.0;

  public static final Logger debug =
      Logger.getLogger("daikon.inv.unary.scalar.OutOfDistributionFloat");

  /** Floor applied to the learned standard deviation to avoid division by (near) zero. */
  private static final double MIN_STD_DEV = 1e-10;

  // Welford's online accumulators; used while learning, then frozen as the learned model.
  private long n = 0;
  private double mean = 0.0;
  private double m2 = 0.0;

  /** True once {@link #n} has reached {@link #dkconfig_learning_samples} and the model is fixed. */
  private boolean frozen = false;

  private double learnedMean = Double.NaN;
  private double learnedStdDev = Double.NaN;

  /** Number of runtime samples flagged as out-of-distribution since freezing. */
  private long oodCount = 0;

  /** Largest |z-score| observed among out-of-distribution samples. */
  private double maxAbsZ = 0.0;

  /** Value that produced {@link #maxAbsZ}. */
  private double worstOodValue = Double.NaN;

  private OutOfDistributionFloat(PptSlice ppt) {
    super(ppt);
  }

  private @Prototype OutOfDistributionFloat() {
    super();
  }

  private static @Prototype OutOfDistributionFloat proto = new @Prototype OutOfDistributionFloat();

  /** Returns the prototype invariant for OutOfDistributionFloat. */
  public static @Prototype OutOfDistributionFloat get_proto() {
    return proto;
  }

  @Override
  public boolean enabled() {
    return dkconfig_enabled;
  }

  @Override
  public OutOfDistributionFloat instantiate_dyn(@Prototype OutOfDistributionFloat this, PptSlice slice) {
    return new OutOfDistributionFloat(slice);
  }

  private double effectiveStdDev() {
    return Math.max(learnedStdDev, MIN_STD_DEV);
  }

  private double zScore(double value) {
    return (value - learnedMean) / effectiveStdDev();
  }

  /** Folds one sample into the Welford accumulators (learning phase only). */
  private void learn(double value, int count) {
    for (int i = 0; i < count; i++) {
      n++;
      double delta = value - mean;
      mean += delta / n;
      double delta2 = value - mean;
      m2 += delta * delta2;
      if (n >= dkconfig_learning_samples) {
        freeze();
        break;
      }
    }
  }

  private void freeze() {
    frozen = true;
    learnedMean = mean;
    learnedStdDev = (n > 1) ? Math.sqrt(m2 / (n - 1)) : 0.0;
  }

  @SideEffectFree
  @Override
  public String format_using(@GuardSatisfied OutOfDistributionFloat this, OutputFormat format) {
    String name = var().name_using(format);

    if (format == OutputFormat.DAIKON) {
      if (!frozen) {
        return name + " ~ learning distribution (" + n + "/" + dkconfig_learning_samples + " samples)";
      }
      String base =
          name + " ~ N(mean=" + learnedMean + ", stddev=" + learnedStdDev + ")";
      if (oodCount == 0) {
        return base + " [no out-of-distribution samples]";
      }
      return base
          + " VIOLATED: "
          + oodCount
          + " out-of-distribution sample(s), worst value="
          + worstOodValue
          + " (z="
          + maxAbsZ
          + ", threshold="
          + dkconfig_z_threshold
          + ")";
    }

    return format_unimplemented(format);
  }

  @Override
  public InvariantStatus check_modified(double value, int count) {
    if (!frozen) {
      return InvariantStatus.NO_CHANGE;
    }
    if (Double.isNaN(value) || Double.isInfinite(value)) {
      return InvariantStatus.NO_CHANGE;
    }
    if (Math.abs(zScore(value)) > dkconfig_z_threshold) {
      return InvariantStatus.FALSIFIED;
    }
    return InvariantStatus.NO_CHANGE;
  }

  @Override
  public InvariantStatus add_modified(double value, int count) {
    if (falsified) {
      return InvariantStatus.FALSIFIED;
    }
    if (Double.isNaN(value) || Double.isInfinite(value)) {
      return InvariantStatus.NO_CHANGE;
    }

    if (!frozen) {
      learn(value, count);
      return InvariantStatus.NO_CHANGE;
    }

    // Detection phase: check the runtime sample against the learned, frozen parameters.
    double z = zScore(value);
    if (Math.abs(z) > dkconfig_z_threshold) {
      oodCount += count;
      if (Math.abs(z) > maxAbsZ) {
        maxAbsZ = Math.abs(z);
        worstOodValue = value;
      }
      falsified = true;
      return InvariantStatus.FALSIFIED;
    }
    return InvariantStatus.NO_CHANGE;
  }

  @Override
  protected double computeConfidence() {
    if (!frozen) {
      return Invariant.CONFIDENCE_UNJUSTIFIED;
    }
    if (oodCount > 0) {
      return Invariant.CONFIDENCE_UNJUSTIFIED;
    }
    return Invariant.CONFIDENCE_JUSTIFIED;
  }

  @Override
  public boolean enoughSamples(@GuardSatisfied OutOfDistributionFloat this) {
    return frozen;
  }

  @Pure
  @Override
  public boolean isSameFormula(Invariant other) {
    return true;
  }

  @Override
  public @Nullable OutOfDistributionFloat merge(List<Invariant> invs, PptSlice parent_ppt) {
    OutOfDistributionFloat first = (OutOfDistributionFloat) invs.get(0);
    OutOfDistributionFloat result = (OutOfDistributionFloat) first.clone();
    result.ppt = parent_ppt;

    long n = result.n;
    double mean = result.mean;
    double m2 = result.m2;

    for (int i = 1; i < invs.size(); i++) {
      OutOfDistributionFloat child = (OutOfDistributionFloat) invs.get(i);

      long combinedN = n + child.n;
      if (combinedN > 0) {
        double delta = child.mean - mean;
        double newMean = (combinedN == 0) ? 0.0 : mean + delta * child.n / combinedN;
        double newM2 = m2 + child.m2 + delta * delta * n * child.n / (double) combinedN;
        n = combinedN;
        mean = newMean;
        m2 = newM2;
      }

      result.oodCount += child.oodCount;
      if (child.maxAbsZ > result.maxAbsZ) {
        result.maxAbsZ = child.maxAbsZ;
        result.worstOodValue = child.worstOodValue;
      }
      if (child.falsified) {
        result.falsified = true;
      }
    }

    result.n = n;
    result.mean = mean;
    result.m2 = m2;
    if (n >= dkconfig_learning_samples) {
      result.freeze();
    } else {
      result.frozen = false;
    }

    result.log("Merged '%s' from %s child invariants", result.format(), invs.size());
    return result;
  }
}
