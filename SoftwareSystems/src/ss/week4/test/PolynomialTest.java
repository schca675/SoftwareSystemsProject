package ss.week4.test;

import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.assertEquals;

import ss.week4.Polynomial;

public class PolynomialTest {
	private Polynomial polly;
    private static final double DELTA = 1e-15;
	private static final double COEFF0 = 1;
	private static final double COEFF1 = 2;
	private static final double COEFF2 = 3;
	private static final double APPLYVAL = 0.5;
	
	@Before
	public void setUp() {
		double[] coeffs = {COEFF0, COEFF1, COEFF2};
		polly = new Polynomial(coeffs);
	}
	
	@Test
	public void testApply() {
		assertEquals(COEFF0 + COEFF1 * APPLYVAL + COEFF2 * Math.pow(APPLYVAL, 2), 
				polly.apply(APPLYVAL), DELTA);
	}
	
	@Test
	public void testDerivative() {
    //    assertTrue(polly.derivative() instanceof Polynomial);
        // This is awful
		assertEquals(5d, polly.derivative().apply(APPLYVAL), DELTA);
	}
	
	@Test
	public void testIntegrand() {
    //    assertTrue(polly.integrand() instanceof Polynomial);
		System.out.println(polly.integrand().apply(APPLYVAL));
		System.out.println(polly.integrand().toString());
		System.out.println(polly.toString());
        // So ugly
		assertEquals(0.875d, polly.integrand().apply(APPLYVAL), DELTA);
	}
}
