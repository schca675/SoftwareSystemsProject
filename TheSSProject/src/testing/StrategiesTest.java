package testing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import model.Board;
import model.RandomStrategy;
import model.Strategy;
import model.TowerCoordinates;

public class StrategiesTest {

	public static final int ID = 1;
	private Strategy randi;
	private Board board;
	
	@Before
	public void setup() {
		randi = new RandomStrategy();
		board = new Board();
	}
	
	@Test
	public void testName() {
		assertEquals("Randi", randi.getName());
	}
	
	@Test
	public void testDetermineMove() {
		TowerCoordinates coord = randi.determineMove(board, ID);
		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
	}
	
}
