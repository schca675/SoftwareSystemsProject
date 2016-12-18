package ss.week4;

public class Homework {
	
	public static void main(String[] args) {
		LinearProduct f1 = new LinearProduct(new Exponent(4), new Constant(4));
		Function f2 = f1.integrand();
		Function f3 = f1.derivative();
		Function f4 = f1.integrand().derivative();
		
		System.out.println("f(x) = " + f1 + ", f(8) =  " + f1.apply(8));
		System.out.println("f(x) = " + f2 + ", f(8) =  " + f2.apply(8));
		System.out.println("f(x) = " + f3 + ", f(8) =  " + f3.apply(8));
		System.out.println("f(x) = " + f4 + ", f(8) =  " + f4.apply(8));
		
		double[] coeffs = {2.0, 5.0, 6.0, 9.0};
		Polynomial f5 = new Polynomial(coeffs);
		Function f6 = f5.integrand();
		Function f7 = f5.derivative();
		Function f8 = f5.integrand().derivative();
		
		System.out.println("f(x) = " + f5 + ", f(8) =  " + f5.apply(8));
		System.out.println("f(x) = " + f6 + ", f(8) =  " + f6.apply(8));
		System.out.println("f(x) = " + f7 + ", f(8) =  " + f7.apply(8));
		System.out.println("f(x) = " + f8 + ", f(8) =  " + f8.apply(8));
	}
}
