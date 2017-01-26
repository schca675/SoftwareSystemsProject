package testing;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Before;
import org.junit.Test;

import exc.IllegalBoardConstructorArgumentsException;
import exc.IllegalCoordinatesException;
import model.Board;

public class BoardTest {
	
	public static final int LENGTH = 5;
	public static final int WIDTH = 7;
	public static final int HEIGHT = 6;
	public static final int WIN = 5;
	public static final int UNLIMITED = Board.UNLIMITED_Z;
	public static final Integer PLAYER1 = 1;
	public static final Integer PLAYER2 = 2;
	/**
	 * Testing variables for default board.
	 * Assuming the default board has equal X-,Y-,Z- and Winning-length.
	 */
	/*@ requires Board.DEFAULT_XDIM == Board.DEFAULT_YDIM 
	  @ == Board.DEFAULT_ZDIM == Board.DEFAULT_WIN;  */
	public static final int MIN = 1;
	public static final int MAX = Board.DEFAULT_DIM;
	//@ requires Board.DEFAULT_DIM > 1;
	public static final int BET = Board.DEFAULT_DIM - 1;
	public static final int TOLOW = 0;
	public static final int TOHIGH = Board.DEFAULT_DIM + 1;
	
	private Board board;
	private Board specialBoard;
	private Board unlimitedBoard;
	
	@Before
	public void setUp() {
		board = new Board();
		try {
			specialBoard = new Board(LENGTH, WIDTH, HEIGHT, WIN);
			unlimitedBoard = new Board(LENGTH, WIDTH, UNLIMITED, WIN);
		} catch (IllegalBoardConstructorArgumentsException e) {
			System.out.println(e.getMessage());
		}
	}

	// <------ Test the constructors ------>
	
	/**
	 * Test the Board constructor with default dimensions.
	 */
	@Test
	public void testDefaultDimension() {
		assertEquals(Board.DEFAULT_DIM, board.xDim);
		assertEquals(Board.DEFAULT_DIM, board.yDim);
		assertEquals(Board.DEFAULT_DIM, board.zDim);
		assertEquals(Board.DEFAULT_WIN, board.winningLength);
	}

	/**
	 * Test the Board Constructor with special dimensions.
	 */
	@Test
	public void testSpecialDimension() {
		assertEquals(LENGTH, specialBoard.xDim);
		assertEquals(WIDTH, specialBoard.yDim);
		assertEquals(HEIGHT, specialBoard.zDim);
		assertEquals(WIN, specialBoard.winningLength);
		assertEquals(UNLIMITED, unlimitedBoard.zDim);
	}
	
	// <------ Test the queries ------>
	
	/**
	 * Test the query CheckMove().
	 */
	@Test 
	public void testCheckMove() {
		assertTrue(board.isValidMove(MIN, MIN));
		assertTrue(board.isValidMove(MAX, MAX));
		assertTrue(board.isValidMove(BET, BET));
		assertFalse(board.isValidMove(TOLOW, TOLOW));
		assertFalse(board.isValidMove(TOLOW, BET));
		assertFalse(board.isValidMove(BET, TOLOW));
		assertFalse(board.isValidMove(TOHIGH, TOHIGH));
		assertFalse(board.isValidMove(TOHIGH, BET));
		assertFalse(board.isValidMove(BET, TOHIGH));		
	}
	
	/**
	 * Test the query CheckCellOwner().
	 */
	@Test
	public void testCheckCellOwner() {
		try {
			assertNull(board.getCellOwner(MIN, MIN, MIN));
			board.makeMove(MIN, MIN, PLAYER2);
			assertEquals(board.getCellOwner(MIN, MIN, MIN), PLAYER2);	
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
			
	}
	
	/**
	 * Test the query isEmptyCell().
	 */
	@Test
	public void testIsEmptyCell() {
		try {
			assertTrue(board.isEmptyCell(MIN, MIN, MIN));
			board.makeMove(MIN, MIN, PLAYER2);
			assertFalse(board.isEmptyCell(MIN, MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
		
	}
	
	/**
	 * Test the query isFull().
	 */
	@Test
	public void testisFull() {
		try {
			assertFalse(board.isFull());
			for (int i = MIN; i <= MAX; i++) {
				for (int j = MIN; j <= MAX; j++) {
					for (int k = MIN; k <= MAX; k++) {
						board.makeMove(i, j, PLAYER2);
					}
				}
			}
			assertTrue(board.isFull());	
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
			
		
	}
	
	/**
	 * Test the query getTowerHeight().
	 */
	@Test
	public void getTowerHeight() {
		try {
			assertEquals(0, board.getTowerHeight(MIN, MAX));
			board.makeMove(MIN, MAX, PLAYER2);
			assertEquals(1, board.getTowerHeight(MIN, MAX));
			board.makeMove(MIN, MAX, PLAYER2);
			assertEquals(2, board.getTowerHeight(MIN, MAX));
			board.makeMove(MIN, MAX, PLAYER2);
			assertEquals(3, board.getTowerHeight(MIN, MAX));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	/**
	 *  Test X - dimension for every Y and every Z layer.
	 */
	@Test 
	public void testHasWonXDir() {
		try {
			for (int z = MIN; z <= MAX; z++) {
				for (int y = MIN; y <= MAX; y++) {
					for (int x = MIN; x <= MAX; x++) {
						board.makeMove(x, y, PLAYER2);
					}
					for (int i = MIN; i <= MAX; i++) {
						assertTrue(board.hasWon(i, y));
					}
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	/**
	 * test X - dimension with different playerIDs.
	 */
	@Test
	public void testHasNotWonXDir() {
		Integer playerID = PLAYER2;
		try {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(i, MIN, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	// Test Y - dimension for every X and every Z layer;
	@Test 
	public void testHasWonYDir() {
		try {
			for (int z = MIN; z <= MAX; z++) {
				for (int x = MIN; x <= MAX; x++) {
					for (int y = MIN; y <= MAX; y++) {
						board.makeMove(x, y, PLAYER2);
					}
					for (int i = 1; i <= 4; i++) {
						assertTrue(board.hasWon(x, i));
					}
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	/**
	 * test Y - dimension with different player IDs.
	 */
	@Test
	public void testHasNotWonYDim() {
		Integer playerID = PLAYER2;
		try {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(MIN, i, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	// Test Z - direction for every X and every Y layer
	@Test 
	public void testHasWonZDir() {
		try {
			for (int x = MIN; x <= MAX; x++) {
				for (int y = MIN; y <= MAX; y++) {
					for (int z = MIN; z <= MAX; z++) {
						board.makeMove(x, y, PLAYER2);
					}
					for (int i = MIN; i <= MAX; i++) {
						assertTrue(board.hasWon(x, y));
					}
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	@Test 
	public void testHasNotWonZDim() {
		Integer playerID = PLAYER2;
		try {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(MIN, i, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	/**
	 *  Test X+Y-direction for every Z-Layer
	 *  One possible winning diagonal per layer.
	 */
	@Test 
	public void testHasWonXpYDir() {
		try {
			for (int z = MIN; z <= MAX; z++) {
				for (int i = MIN; i <= MAX; i++) {
					board.makeMove(i, i, PLAYER2);
				}
				for (int j = MIN; j <= MAX; j++) {
					assertTrue(board.hasWon(j, j));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	@Test
	public void testHasNotWonXpYDir() {
		Integer playerID = PLAYER2;
		try {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(i, i, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	/**
	 *  Test X-Y-direction for every Z-Layer
	 *  One possible winning diagonal per layer.
	 */
	@Test 
	public void testHasWonXmYDir() {		
		try {
			for (int z = MIN; z <= MAX; z++) {
				for (int i = 0; i < MAX; i++) {
					board.makeMove(MAX - i, MIN + i, PLAYER2);
				}
				for (int j = 0; j < MAX; j++) {
					assertTrue(board.hasWon(MAX - j, MIN + j, z));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	@Test
	public void testHasNotWonXmYDir() {
		try {
			Integer playerID = PLAYER2;
			for (int i = 0; i < MAX; i++) {
				board.makeMove(MAX - i, MIN + i, playerID);
				playerID = PLAYER1;
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing XmY");
		}
	}
	
	/**
	 * Test X+Z-direction for every Y-Layer.
	 * One possible winning diagonal per layer.
	 */
	@Test 
	public void testHasWonXpZDir() {
		try {
			for (int y = MIN; y <= MAX; y++) {
				for (int x = MIN; x <= MAX; x++) {
					for (int z = MIN; z <= x; z++) {
						board.makeMove(x, y, PLAYER2);
					}
				}
				for (int i = MIN; i <= MAX; i++) {
					assertTrue(board.hasWon(i, y));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing XpZ");
		}
	}
	
	@Test
	public void testHasNotWonXpZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MIN; z <= x; z++) {
					board.makeMove(x, MIN, playerID);
					playerID = PLAYER1;
				}
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	/**
	 * Test X-Z-direction for every Y-Layer.
	 * One possible winning diagonal per layer.
	 */
	@Test 
	public void testHasWonXmZDir() {
		//Short Test, not elaborated (to delete)
		try {
//			board.makeMove(4, 1, PLAYER2);
//			board.makeMove(3, 1, PLAYER2);
//			board.makeMove(3, 1, PLAYER2);
//			board.makeMove(2, 1, PLAYER2);
//			board.makeMove(2, 1, PLAYER2);
//			board.makeMove(2, 1, PLAYER2);
//			board.makeMove(1, 1, PLAYER2);
//			board.makeMove(1, 1, PLAYER2);
//			board.makeMove(1, 1, PLAYER2);
//			board.makeMove(1, 1, PLAYER2);		
//			assertTrue(board.hasWon(4, 1));
			//board.reset();
			for (int y = MIN; y <= MAX; y++) {
				for (int x = MIN; x <= MAX; x++) {
					for (int z = MAX; z >= x; z--) {
						board.makeMove(x, y, PLAYER2);
					}
				}
				for (int i = MIN; i <= MAX; i++) {
					assertTrue(board.hasWon(i, y, MAX + 1 - i));
				}
			}
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing");
		}
	}
	
	@Test
	public void testHasNotWonXmZDir() {
		try {
			Integer playerID = PLAYER2;
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MAX; z >= x; z--) {
					board.makeMove(x, MIN, playerID);
					if (playerID == PLAYER2) {
						playerID = PLAYER1;
					} else {
						playerID = PLAYER2;
					}
				}
			}
			assertFalse(board.hasWon(MIN, MIN));
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing XmZ");
		}
	}
	
	//Test Y+Z-direction
	@Test 
	public void testHasWonYpZDir() {
	}
	
	//Test Y-Z-direction
	@Test 
	public void testHasWonYmZDir() {
		
	}
	
	//test X+Y+Z-direction
	@Test 
	public void testHasWonXpYpZDir() {
		
	}
	
	//Test X+Y-Z-direction
	@Test 
	public void testHasWonXpYmZDir() {
		
	}
	
	//Test X-Y+Z-direction
	@Test 
	public void testHasWonXmYpZDir() {
		
	}
	
	//Test X-Y-Z-direction
	@Test 
	public void testHasWonXmYmZDir() {
		
	}
	
	@Test
	public void testisValidTowerDef() {
		assertTrue(board.isValidTower(1, 1));
		assertTrue(board.isValidTower(1, 3));
		assertTrue(board.isValidTower(2, 1));
		assertTrue(board.isValidTower(4, 4));
		assertTrue(board.isValidTower(4, 3));
		assertTrue(board.isValidTower(2, 4));
		assertFalse(board.isValidTower(0, 0));
		assertFalse(board.isValidTower(0, 1));
		assertFalse(board.isValidTower(3, 0));
		assertFalse(board.isValidTower(5, 2));
		assertFalse(board.isValidTower(4, 5));
		assertFalse(board.isValidTower(5, 5));		
	}
	
	@Test
	public void testisValidTowerSpec() {		
		assertTrue(specialBoard.isValidTower(5, 7));
		assertFalse(specialBoard.isValidTower(6, 5));
		assertFalse(specialBoard.isValidTower(3, 8));
	}
	
	@Test
	public void testisValidCell() {
		assertTrue(board.isValidCell(1, 1, 1));
		assertTrue(board.isValidCell(4, 1, 1));
		assertTrue(board.isValidCell(1, 4, 1));
		assertTrue(board.isValidCell(1, 1, 4));
		assertTrue(board.isValidCell(4, 4, 4));
		assertTrue(board.isValidCell(2, 3, 2));
		assertFalse(board.isValidCell(1, 1, -1));
		assertFalse(board.isValidCell(1, -1, 1));
		assertFalse(board.isValidCell(-1, 1, 1));
		assertFalse(board.isValidCell(-1, -1, -1));
		assertFalse(board.isValidCell(5, 1, 1));
		assertFalse(board.isValidCell(1, 5, 1));
		assertFalse(board.isValidCell(1, 1, 5));
	}

	// <------ Test the commands ------>
	
	@Test
	public void testMakeMove() {
		try {
			board.makeMove(1, 1, PLAYER2);
			assertFalse(board.isEmptyCell(1, 1, 1));
			assertTrue(board.isEmptyCell(1, 1, 2));
			assertTrue(board.isEmptyCell(1, 1, 3));
			assertTrue(board.isEmptyCell(1, 1, 4));
			board.makeMove(1, 1, PLAYER2);
			assertEquals(board.getCellOwner(1, 1, 1), PLAYER2);
			assertEquals(board.getCellOwner(1, 1, 2), PLAYER2);
			assertNotEquals(board.getCellOwner(1, 1, 3), PLAYER2);
		} catch (IllegalCoordinatesException e) {
			System.out.println("Exceptions while testing 2");
		}
	}
	
	@Test
	public void testDeepDataCopy() {
		List<List<Integer>> data = board.deepDataCopy();
		
	}
//	@Test
//	public void testReset() {
//		for (int i = 1; i <= 4; i++) {
//			for (int j = 1; j <= 4; j++) {
//				for (int k = 1; k <= 4; k++) {
//					assertTrue(board.isEmptyCell(i, j, k));
//				}
//			}
//		}
//		board.makeMove(1, 2, PLAYER2);
//		board.makeMove(1, 2, PLAYER2);
//		board.makeMove(1, 2, PLAYER2);	
//		board.makeMove(3, 2, PLAYER2);
//		board.makeMove(4, 2, PLAYER2);
//		board.reset();
//		for (int i = 1; i <= 4; i++) {
//			for (int j = 1; j <= 4; j++) {
//				for (int k = 1; k <= 4; k++) {
//					assertTrue(board.isEmptyCell(i, j, k));
//				}
//			}
//		}
//	}
	
	
}
