package daikon.derive.binary;

import daikon.ProglangType;
import daikon.ValueTuple;
import daikon.VarInfo;
import daikon.derive.Derivation;
import daikon.derive.ValueAndModified;
import java.util.logging.Logger;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;

/**
 * Represents the Pearson statistical correlation between two base variables.
 * This derived variable computes the correlation coefficient of two sequences of numbers.
 */
public final class StatisticalCorrelation extends BinaryDerivation {
  static final long serialVersionUID = 20020122L;

  /** Debug tracer. */
  public static final Logger debug = Logger.getLogger("daikon.derive.binary.StatisticalCorrelation");

  // Variables starting with dkconfig_ should only be set via the
  // daikon.config.Configuration interface.
  /** Boolean. True iff StatisticalCorrelation derived variables should be created. */
  public static boolean dkconfig_enabled = false;

  @Override
  public VarInfo var1(@GuardSatisfied StatisticalCorrelation this) {
    return base1;
  }

  @Override
  public VarInfo var2(@GuardSatisfied StatisticalCorrelation this) {
    return base2;
  }

  /**
   * Create a new StatisticalCorrelation that represents the Pearson correlation between two base
   * variables.
   *
   * @param vi1 base variable 1
   * @param vi2 base variable 2
   */
  public StatisticalCorrelation(VarInfo vi1, VarInfo vi2) {
    super(vi1, vi2);
  }

  /**
   * Computes the Pearson correlation coefficient between two arrays.
   *
   * @param arr1 first array
   * @param arr2 second array
   * @return the correlation coefficient or null if unable to compute
   */
  private static Double computeCorrelation(long[] arr1, long[] arr2) {
    if (arr1 == null || arr2 == null || arr1.length != arr2.length || arr1.length < 2) {
      return null;
    }

    int n = arr1.length;
    double sum_x = 0, sum_y = 0, sum_x2 = 0, sum_y2 = 0, sum_xy = 0;

    for (int i = 0; i < n; i++) {
      double x = arr1[i];
      double y = arr2[i];
      sum_x += x;
      sum_y += y;
      sum_x2 += x * x;
      sum_y2 += y * y;
      sum_xy += x * y;
    }

    double numerator = n * sum_xy - sum_x * sum_y;
    double denominator = Math.sqrt((n * sum_x2 - sum_x * sum_x) * (n * sum_y2 - sum_y * sum_y));

    if (denominator == 0) {
      return null;
    }

    return numerator / denominator;
  }

  /**
   * Computes the Pearson correlation coefficient between two double arrays.
   *
   * @param arr1 first array
   * @param arr2 second array
   * @return the correlation coefficient or null if unable to compute
   */
  private static Double computeCorrelation(double[] arr1, double[] arr2) {
    if (arr1 == null || arr2 == null || arr1.length != arr2.length || arr1.length < 2) {
      return null;
    }

    int n = arr1.length;
    double sum_x = 0, sum_y = 0, sum_x2 = 0, sum_y2 = 0, sum_xy = 0;

    for (int i = 0; i < n; i++) {
      double x = arr1[i];
      double y = arr2[i];
      sum_x += x;
      sum_y += y;
      sum_x2 += x * x;
      sum_y2 += y * y;
      sum_xy += x * y;
    }

    double numerator = n * sum_xy - sum_x * sum_y;
    double denominator = Math.sqrt((n * sum_x2 - sum_x * sum_x) * (n * sum_y2 - sum_y * sum_y));

    if (denominator == 0) {
      return null;
    }

    return numerator / denominator;
  }

  @Override
  public ValueAndModified computeValueAndModifiedImpl(ValueTuple full_vt) {
    Object val1 = var1().getValue(full_vt);
    Object val2 = var2().getValue(full_vt);

    int mod = ValueTuple.UNMODIFIED;
    int mod1 = base1.getModified(full_vt);
    int mod2 = base2.getModified(full_vt);

    if (mod1 == ValueTuple.MODIFIED || mod2 == ValueTuple.MODIFIED) {
      mod = ValueTuple.MODIFIED;
    }

    if (val1 == null || val2 == null) {
      return new ValueAndModified(null, mod);
    }

    Double result = null;

    if (var1().rep_type == ProglangType.INT_ARRAY) {
      result = computeCorrelation((long[]) val1, (long[]) val2);
    } else if (var1().rep_type == ProglangType.DOUBLE_ARRAY) {
      result = computeCorrelation((double[]) val1, (double[]) val2);
    } else {
      throw new Error("Attempted to compute correlation on unknown array type:" + var1().rep_type + " and " + var2().rep_type);
    }

    return new ValueAndModified(result, mod);
  }

  @Override
  protected VarInfo makeVarInfo() {
    return VarInfo.make_function("correlation", var1(), var2());
  }

  @SideEffectFree
  @Override
  public String toString(@GuardSatisfied StatisticalCorrelation this) {
    return "[StatisticalCorrelation of " + var1().name() + " " + var2().name() + "]";
  }

  @Pure
  @Override
  public boolean isSameFormula(Derivation other) {
    return (other instanceof StatisticalCorrelation);
  }

  @SideEffectFree
  @Override
  public String esc_name(String index) {
    return String.format("StatisticalCorrelation[%s,%s]", var1().esc_name(), var2().esc_name());
  }
}
