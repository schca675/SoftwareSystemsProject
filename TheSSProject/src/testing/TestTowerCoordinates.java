package testing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import model.RandomStrategy;
import model.TowerCoordinates;

public class TestTowerCoordinates {

	private TowerCoordinates coordA;
	private TowerCoordinates coordB;
	private TowerCoordinates coordC;
	private TowerCoordinates coordD;
	private Object coordE;
	private Object other;
	
	/**
	 * Do the setup for the Tower Coordinates Test.
	 */
	@Before
	public void setup() {
		coordA = new TowerCoordinates(1, 2);
		coordB = new TowerCoordinates(1, 2);
		coordC = new TowerCoordinates(2, 1);
		coordD = new TowerCoordinates(1, 3);
		coordE = new TowerCoordinates(1, 2);
		other = new RandomStrategy();
	}
	
	/**
	 * Test the GetX method.
	 */
	@Test
	public void testGetX() {
		assertEquals(1, coordA.getX());
	}
	
	/**
	 * Test the GetY method.
	 */
	@Test 
	public void testGetY() {
		assertEquals(2, coordA.getY());
	}
	
	/**
	 * Test if equal TowerCoordinates are recognised as equal.
	 */
	@Test
	public void testEquals() {
		assertTrue(coordA.equals(coordB));
		assertTrue(coordB.equals(coordA));
		assertTrue(coordA.equals(coordE));
		assertFalse(coordA.equals(coordC));
		assertFalse(coordA.equals(coordD));
		assertFalse(coordA.equals(other));
	}
	
	/**
	 * Test the representation, should print the x and y coordinates on the console.
	 */
	@Test
	public void testToString() {
		System.out.println(coordA.toString());
	}
}
