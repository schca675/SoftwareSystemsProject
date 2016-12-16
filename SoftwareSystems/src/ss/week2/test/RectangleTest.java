package ss.week2.test;

import org.junit.Before;
import org.junit.Test;
import ss.week2.Rectangle;

import static org.junit.Assert.assertEquals;

public class RectangleTest {
	private int l1;
	private int w1;
	private int l2;
	private int w2;
	private Rectangle rectangle1;
	private Rectangle rectangle2;

	/*
	 * Set up, creating certain rectangles.
	 */
	@Before
	public void setUp() {
		l1 = 5;
		w1 = 7;
		l2 = 8;
		w2 = 3;
		rectangle1 = new Rectangle(l1, w1);
		rectangle2 = new Rectangle(l2, w2);
	}

	/**
	 * Test if the initial condition complies to the specification.
	 */
	@Test
	public void testLength() {
		assertEquals(l1, rectangle1.length());
		assertEquals(l2, rectangle2.length());
	}
	
	@Test
	public void testWidth() {
		assertEquals(w1, rectangle1.width());
		assertEquals(w2, rectangle2.width());
	}	
	
	@Test
	public void testArea() {	
		assertEquals(35, rectangle1.area());
		assertEquals(24, rectangle2.area());
	}
	@Test
	public void testPerimeter() {
		assertEquals(24, rectangle1.perimeter());
		assertEquals(22, rectangle2.perimeter());
	}
}