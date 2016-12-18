package ss.week4;

public class Polynomial implements Function, Integrandable {
	private LinearProduct[] polly;
	
	// coeffs[0], coeffs[1], coeffs[2], ..., coeffs[coeffs.length] 
	// represent a0 + a1*x + a2*x^2 + ... + an*x^n
	public Polynomial(double[] coeffs) {
		polly = new LinearProduct[coeffs.length];
		for (int i = 0; i < coeffs.length; i++) {
			polly[i] = new LinearProduct(new Exponent(i), new Constant(coeffs[i]));
		}
	}

	@Override
	public double apply(double argument) {
		double sum = 0;
		for (int i = 0; i < polly.length; i++) {
			sum = sum + polly[i].apply(argument);
		}
		return sum;
	}

	@Override
	public Function derivative() {
		Function derivative = new Constant(0);
		for (int i = 0; i < polly.length; i++) {
			derivative = new Sum(derivative, polly[i].derivative());
		}
		return derivative;
	}

	@Override
	public Function integrand() {
		Function integrand = new Constant(0);
		for (int i = 0; i < polly.length; i++) {
			integrand = new Sum(integrand, polly[i].integrand());
		}
		return integrand;
	}
	
	@Override
	public String toString() {
		String henk = "";
		for (int i = 0; i < polly.length; i++) {
			henk = henk + polly[i].toString() + " + ";
		}
		return henk;
	}
}
