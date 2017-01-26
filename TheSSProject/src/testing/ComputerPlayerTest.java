package testing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Before;
import org.junit.Test;

import exc.TowerCoordinates;
import model.Board;
import model.ComputerPlayer;
import model.RandomStrategy;
import model.Strategy;

public class ComputerPlayerTest {

	public static final int TESTTIMES = 2;
	public static final int ID = 1;
	private Board board;
	private ComputerPlayer randi;
	private Strategy random;
	
	@Before
	public void setup() {
		random = new RandomStrategy();
		randi = new ComputerPlayer(random, ID);
		board = new Board();
	}
	
	@Test
	public void testName() {
		assertEquals(random.getName(), randi.name);
	}
	
	@Test
	public void testID() {
		assertEquals(ID, randi.playerID);
	}
	
	@Test
	public void testDetermineMove() {
		TowerCoordinates coord = randi.determineMove(board);
		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
	}
	
//	@Test
//	public void testDetermineRandisMove1() {
//		TowerCoordinates coord = randi.determineMove(board);
//		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
//	}
//	
//	@Test
//	public void testDetermineRandisMove2() {
//		TowerCoordinates coord = randi.determineMove(board);
//		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
//	}
//	
//	@Test
//	public void testDetermineRandisMove3() {
//		TowerCoordinates coord = randi.determineMove(board);
//		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
//	}
//	
//	@Test
//	public void testDetermineRandisMove4() {
//		TowerCoordinates coord = randi.determineMove(board);
//		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
//	}
//	
//	@Test
//	public void testDetermineRandisMove5() {
//		TowerCoordinates coord = randi.determineMove(board);
//		assertTrue(board.isValidMove(coord.getX(), coord.getY()));
//	}
}
