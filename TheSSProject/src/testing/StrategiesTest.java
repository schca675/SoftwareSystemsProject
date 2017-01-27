package testing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import exc.IllegalCoordinatesException;
import model.Board;
import model.RandomStrategy;
import model.SmartStrategy;
import model.Strategy;
import model.TowerCoordinates;

public class StrategiesTest {

	public static final int ID = 1;
	private Strategy randi;
	private Strategy trams;
	private Board board;
	
	@Before
	public void setup() {
		randi = new RandomStrategy();
		trams = new SmartStrategy();
		board = new Board();
	}
	
	/**
	 * Test the getName() method of the random strategy.
	 */
	@Test
	public void testRandisName() {
		assertEquals("Randi", randi.getName());
	}
	
	/**
	 * Test the determine move method of the random strategy.
	 */
	@Test
	public void testRandisDetermineMove() {
		TowerCoordinates coord = randi.determineMove(board, ID);
		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
	}
	
	/**
	 * Test the getName() method of the smart strategy.
	 */
	@Test
	public void testTramsName() {
		assertEquals("Trams", trams.getName());
	}
	
	/**
	 * Test if the determine move method of the smart strategy returns a valid move.
	 */
	@Test
	public void testTramsDetermineMoveisValid() {
		TowerCoordinates coord = trams.determineMove(board, ID);
		assertTrue(board.isValidMove(coord.getX(), coord.getY()));		
	}
	
	/**
	 * Test if the determine move method of the smart strategy returns the winning move, if 
	 * the entered ID can win with the move.
	 * @throws IllegalCoordinatesException if a invalid move on the board is made (impossible). 
	 */
	@Test
	public void testTramsDetermineMove() throws IllegalCoordinatesException {
		TowerCoordinates choice = new TowerCoordinates(1, 1);
		board.makeMove(choice.getX(), choice.getY(), ID);
		board.makeMove(choice.getX(), choice.getY(), ID);
		board.makeMove(choice.getX(), choice.getY(), ID);
		TowerCoordinates coord = trams.determineMove(board, ID);
		System.out.println("Returned: " + coord.toString());
		System.out.println("Should return: " + choice.toString());
		assertEquals(choice, coord);
	}
	
}
