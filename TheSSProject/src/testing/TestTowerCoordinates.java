package testing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import model.TowerCoordinates;

public class TestTowerCoordinates {

	private TowerCoordinates coordA;
	private TowerCoordinates coordB;
	private TowerCoordinates coordC;
	
	@Before
	public void setup() {
		coordA = new TowerCoordinates(1, 2);
		coordB = new TowerCoordinates(1, 2);
		coordC = new TowerCoordinates(2, 1);
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
		assertFalse(coordA.equals(coordC));
	}
}
