package ss.week4;

public class Exponent implements Function, Integrandable {
	private int exponent;
	
	public Exponent(int exponent) {
		this.exponent = exponent;
	}

	@Override
	public double apply(double argument) {
		return Math.pow(argument, exponent);
	}

	@Override
	public Function derivative() {
		return new LinearProduct(new Exponent(exponent - 1), new Constant(exponent));
	}
	
	@Override
	public Function integrand() {
		return new LinearProduct(new Exponent(exponent + 1), new Constant(1 / (exponent + 1.0)));
	}
	
	@Override
	public String toString() {
		return "x^" + exponent;
	}
}
