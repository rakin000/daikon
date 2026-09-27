package daikon.inv.unary.scalar;

import daikon.PptSlice;
import daikon.inv.Invariant;
import daikon.inv.InvariantStatus;
import daikon.inv.OutputFormat;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;
import org.checkerframework.framework.qual.Unused;
import typequals.prototype.qual.Prototype;

/**
 * Trend is a unary invariant over a scalar variable that tracks how each observed value compares
 * to the immediately preceding value of the same variable, in the order samples arrive at this
 * program point. It detects three trends:
 *
 * <ul>
 *   <li>AlwaysNondecreasing: every value is {@code >=} the value that preceded it.
 *   <li>AlwaysNonincreasing: every value is {@code <=} the value that preceded it.
 *   <li>NeverChanging: every value equals the value that preceded it. This is the special case
 *       where both of the above hold simultaneously.
 * </ul>
 *
 * The invariant is falsified as soon as one sample is strictly greater than its predecessor and
 * some other sample (earlier or later) is strictly less than its predecessor, since at that point
 * neither monotonic direction can hold.
 */
public class Trend extends SingleScalar {

  private static final long serialVersionUID = 20260921L;

  // Variables starting with dkconfig_ should only be set via the
  // daikon.config.Configuration interface.
  /** Boolean. True iff Trend invariants should be considered. */
  public static boolean dkconfig_enabled = Invariant.invariantEnabledDefault;

  /** True as long as no sample has decreased relative to its predecessor. */
  @Unused(when = Prototype.class)
  private boolean nondecreasing;

  /** True as long as no sample has increased relative to its predecessor. */
  @Unused(when = Prototype.class)
  private boolean nonincreasing;

  /** True once at least one sample has been seen. */
  @Unused(when = Prototype.class)
  private boolean hasPrevious;

  /** The most recently seen value. Meaningful only when {@link #hasPrevious} is true. */
  @Unused(when = Prototype.class)
  private long previousValue;

  protected Trend(PptSlice ppt) {
    super(ppt);
    nondecreasing = true;
    nonincreasing = true;
    hasPrevious = false;
  }

  protected @Prototype Trend() {
    super();
  }

  private static @Prototype Trend proto = new @Prototype Trend();

  /** Returns the prototype invariant for Trend. */
  public static @Prototype Trend get_proto() {
    return proto;
  }

  @Override
  public Trend instantiate_dyn(@Prototype Trend this, PptSlice slice) {
    return new Trend(slice);
  }

  @Override
  public boolean enabled() {
    return dkconfig_enabled;
  }

  @Override
  public InvariantStatus add_modified(long value, int count) {
    if (hasPrevious) {
      if (value < previousValue) {
        nondecreasing = false;
      }
      if (value > previousValue) {
        nonincreasing = false;
      }
    }
    previousValue = value;
    hasPrevious = true;

    if (!nondecreasing && !nonincreasing) {
      return InvariantStatus.FALSIFIED;
    }
    return InvariantStatus.NO_CHANGE;
  }

  @Override
  public InvariantStatus check_modified(long value, int count) {
    if (!hasPrevious) {
      return InvariantStatus.NO_CHANGE;
    }
    boolean stillNondecreasing = nondecreasing && (value >= previousValue);
    boolean stillNonincreasing = nonincreasing && (value <= previousValue);
    if (!stillNondecreasing && !stillNonincreasing) {
      return InvariantStatus.FALSIFIED;
    }
    return InvariantStatus.NO_CHANGE;
  }

  /** Returns true if every sample has equaled its predecessor (the NeverChanging trend). */
  @Pure
  public boolean isNeverChanging(@GuardSatisfied Trend this) {
    return nondecreasing && nonincreasing;
  }

  /** Returns true if every sample has been {@code >=} its predecessor. */
  @Pure
  public boolean isAlwaysNondecreasing(@GuardSatisfied Trend this) {
    return nondecreasing;
  }

  /** Returns true if every sample has been {@code <=} its predecessor. */
  @Pure
  public boolean isAlwaysNonincreasing(@GuardSatisfied Trend this) {
    return nonincreasing;
  }

  @SideEffectFree
  @Override
  public String format_using(@GuardSatisfied Trend this, OutputFormat format) {
    String varname = var().name_using(format);

    if (isNeverChanging()) {
      if (format.isJavaFamily() || (format == OutputFormat.ESCJAVA)
          || (format == OutputFormat.CSHARPCONTRACT)) {
        return "\\old(" + varname + ") == " + varname;
      }
      return varname + " is never changing";
    } else if (isAlwaysNondecreasing()) {
      if (format.isJavaFamily() || (format == OutputFormat.ESCJAVA)
          || (format == OutputFormat.CSHARPCONTRACT)) {
        return "\\old(" + varname + ") <= " + varname;
      }
      return varname + " is always nondecreasing";
    } else if (isAlwaysNonincreasing()) {
      if (format.isJavaFamily() || (format == OutputFormat.ESCJAVA)
          || (format == OutputFormat.CSHARPCONTRACT)) {
        return "\\old(" + varname + ") >= " + varname;
      }
      return varname + " is always nonincreasing";
    } else {
      // Should not normally be reached: the invariant falsifies itself once
      // neither direction can hold.
      return format_unimplemented(format);
    }
  }

  @Override
  protected double computeConfidence() {
    // Model each adjacent pair of samples as independently having a 50%
    // chance of continuing the trend by chance (a rough approximation, as in
    // Positive.computeConfidence). With n samples there are n-1 adjacent
    // comparisons, so the chance of a spurious monotonic run is (.5)^(n-1).
    long pairs = ppt.num_samples() - 1;
    if (pairs <= 0) {
      return Invariant.CONFIDENCE_UNJUSTIFIED;
    }
    return 1 - Math.pow(.5, pairs);
  }

  @Pure
  @Override
  public boolean isSameFormula(Invariant o) {
    Trend other = (Trend) o;
    return (nondecreasing == other.nondecreasing) && (nonincreasing == other.nonincreasing);
  }
}
