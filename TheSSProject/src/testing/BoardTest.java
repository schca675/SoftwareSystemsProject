package testing;

import org.junit.Before;
import org.junit.Test;
import static org.junit.Assert.*;

import model.Board;
import model.PlayerID;

public class BoardTest {
	
	public static final int LENGTH = 5;
	public static final int WIDTH = 7;
	public static final int HEIGHT = 6;
	public static final int WIN = 5;
	/**
	 * Testing variables for default board.
	 * Assuming the default board has equal X-,Y-,Z- and Winning-length.
	 */
	/*@ requires Board.DEFAULT_XDIM == Board.DEFAULT_YDIM 
	  @ == Board.DEFAULT_ZDIM == Board.DEFAULT_WIN;  */
	public static final int MIN = 1;
	public static final int MAX = Board.DEFAULT_XDIM;
	//@ requires Board.DEFAULT_XDIM > 1;
	public static final int BET = Board.DEFAULT_XDIM - 1;
	public static final int TOLOW = 0;
	public static final int TOHIGH = Board.DEFAULT_XDIM + 1;
	
	private Board<PlayerID> board;
	private Board<PlayerID> specialBoard;
	
	@Before
	public void setUp() {
		board = new Board<PlayerID>();
		specialBoard = new Board<PlayerID>(LENGTH, WIDTH, HEIGHT, WIN);
	}

	// <------ Test the constructors ------>
	 
	@Test
	public void testDefaultDimension() {
		assertEquals(Board.DEFAULT_XDIM, board.xDim);
		assertEquals(Board.DEFAULT_YDIM, board.yDim);
		assertEquals(Board.DEFAULT_ZDIM, board.zDim);
		assertEquals(Board.DEFAULT_WIN, board.winningLength);
	}

	@Test
	public void testSpecialDimension() {
		assertEquals(LENGTH, specialBoard.xDim);
		assertEquals(WIDTH, specialBoard.yDim);
		assertEquals(HEIGHT, specialBoard.zDim);
		assertEquals(WIN, specialBoard.winningLength);
	}
	
	// <------ Test the queries ------>
	
	@Test 
	public void testCheckMove() {
		assertTrue(board.checkMove(MIN, MIN));
		assertTrue(board.checkMove(MAX, MAX));
		assertTrue(board.checkMove(BET, BET));
		assertFalse(board.checkMove(TOLOW, TOLOW));
		assertFalse(board.checkMove(TOLOW, BET));
		assertFalse(board.checkMove(BET, TOLOW));
		assertFalse(board.checkMove(TOHIGH, TOHIGH));
		assertFalse(board.checkMove(TOHIGH, BET));
		assertFalse(board.checkMove(BET, TOHIGH));		
	}
	
	@Test
	public void testCheckCellOwner() {
		assertNull(board.getCellOwner(MIN, MIN, MIN));
		board.makeMove(MIN, MIN, PlayerID.O);
		assertEquals(board.getCellOwner(MIN, MIN, MIN), PlayerID.O);		
	}
	
	@Test
	public void testIsEmptyCell() {
		assertTrue(board.isEmptyCell(MIN, MIN, MIN));
		board.makeMove(MIN, MIN, PlayerID.O);
		assertFalse(board.isEmptyCell(MIN, MIN, MIN));
	}
	
	@Test
	public void testisFull() {
		assertFalse(board.isFull());
		for (int i = MIN; i <= MAX; i++) {
			for (int j = MIN; j <= MAX; j++) {
				for (int k = MIN; k <= MAX; k++) {
					board.makeMove(i, j, PlayerID.O);
				}
			}
		}
		assertTrue(board.isFull());		
	}
	
	@Test
	public void getTowerHeight() {
		assertEquals(0, board.getTowerHeight(MIN, MAX));
		board.makeMove(MIN, MAX, PlayerID.O);
		assertEquals(1, board.getTowerHeight(MIN, MAX));
		board.makeMove(MIN, MAX, PlayerID.O);
		assertEquals(2, board.getTowerHeight(MIN, MAX));
		board.makeMove(MIN, MAX, PlayerID.O);
		assertEquals(3, board.getTowerHeight(MIN, MAX));
	}
	
	// Test X - dimension for every Y and every Z layer;
	@Test 
	public void testHasWonXDir() {
		for (int z = MIN; z <= MAX; z++) {
			for (int y = MIN; y <= MAX; y++) {
				for (int x = MIN; x <= MAX; x++) {
					board.makeMove(x, y, PlayerID.O);
				}
				for (int i = MIN; i <= MAX; i++) {
					assertTrue(board.hasWon(i, y, z));
				}
			}
		}
		board.reset();
		PlayerID playerID = PlayerID.O;
		for (int i = MIN; i <= MAX; i++) {
			board.makeMove(i, MIN, playerID);
			playerID = playerID.other();
		}
		assertFalse(board.hasWon(MIN, MIN, MIN));
	}
	
	// Test Y - dimension for every X and every Z layer;
	@Test 
	public void testHasWonYDir() {
		for (int z = MIN; z <= MAX; z++) {
			for (int x = MIN; x <= MAX; x++) {
				for (int y = MIN; y <= MAX; y++) {
					board.makeMove(x, y, PlayerID.O);
				}
				for (int i = 1; i <= 4; i++) {
					assertTrue(board.hasWon(x, i, z));
				}
			}
		}
		board.reset();
		PlayerID playerID = PlayerID.O;
		for (int i = MIN; i <= MAX; i++) {
			board.makeMove(MIN, i, playerID);
			playerID = playerID.other();
		}
		assertFalse(board.hasWon(MIN, MIN, MIN));
		
	}
	
	// Test Z - direction for every X and every Y layer
	@Test 
	public void testHasWonZDir() {
		for (int x = MIN; x <= MAX; x++) {
			for (int y = MIN; y <= MAX; y++) {
				for (int z = MIN; z <= MAX; z++) {
					board.makeMove(x, y, PlayerID.O);
				}
				for (int i = MIN; i <= MAX; i++) {
					assertTrue(board.hasWon(x, y, i));
				}
			}
		}
		board.reset();
		PlayerID playerID = PlayerID.O;
		for (int i = MIN; i <= MAX; i++) {
			board.makeMove(MIN, i, playerID);
			playerID = playerID.other();
		}
		assertFalse(board.hasWon(MIN, MIN, MIN));
	}
	
	// Test X+Y-direction for every Z-Layer
	// One possible winning diagonal per layer.
	@Test 
	public void testHasWonXpYDir() {
		for (int z = MIN; z <= MAX; z++) {
			for (int i = MIN; i <= MAX; i++) {
				board.makeMove(i, i, PlayerID.O);
			}
			for (int j = MIN; j <= MAX; j++) {
				assertTrue(board.hasWon(j, j, z));
			}
		}
		board.reset();
		PlayerID playerID = PlayerID.O;
		for (int i = MIN; i <= MAX; i++) {
			board.makeMove(i, i, playerID);
			playerID = playerID.other();
		}
		assertFalse(board.hasWon(MIN, MIN, MIN));
	}
	
	// Test X-Y-direction for every Z-Layer
	// One possible winning diagonal per layer.
	@Test 
	public void testHasWonXmYDir() {		
		for (int z = MIN; z <= MAX; z++) {
			for (int i = 0; i < MAX; i++) {
				board.makeMove(MAX - i, MIN + i, PlayerID.O);
			}
			for (int j = 0; j < MAX; j++) {
				assertTrue(board.hasWon(MAX - j, MIN + j, z));
			}
		}
		board.reset();
		PlayerID playerID = PlayerID.O;
		for (int i = 0; i < MAX; i++) {
			board.makeMove(MAX - i, MIN + i, PlayerID.O);
			playerID = playerID.other();
		}
		assertFalse(board.hasWon(MIN, MIN, MIN));
	}
	
	//Test X+Z-direction for every Y-Layer;
	// One possible winning diagonal per layer.
	@Test 
	public void testHasWonXpZDir() {
		for (int y = MIN; y <= MAX; y++) {
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MIN; z <= x; z++) {
					board.makeMove(x, y, PlayerID.O);
				}
			}
			for (int i = MIN; i <= MAX; i++) {
				assertTrue(board.hasWon(i, y, i));
			}
		}
		board.reset();
		PlayerID playerID = PlayerID.O;
		for (int x = MIN; x <= MAX; x++) {
			for (int z = MIN; z <= x; z++) {
				board.makeMove(x, MIN, playerID);
				playerID = playerID.other();
			}
		}
		assertFalse(board.hasWon(MIN, MIN, MIN));
	}
	
	//Test X-Z-direction for every Y-Layer;
	// One possible winning diagonal per layer.
	@Test 
	public void testHasWonXmZDir() {
		//Short Test, not elaborated (to delete)
		board.makeMove(4, 1, PlayerID.O);
		board.makeMove(3, 1, PlayerID.O);
		board.makeMove(3, 1, PlayerID.O);
		board.makeMove(2, 1, PlayerID.O);
		board.makeMove(2, 1, PlayerID.O);
		board.makeMove(2, 1, PlayerID.O);
		board.makeMove(1, 1, PlayerID.O);
		board.makeMove(1, 1, PlayerID.O);
		board.makeMove(1, 1, PlayerID.O);
		board.makeMove(1, 1, PlayerID.O);		
		assertTrue(board.hasWon(4, 1, 1));
		board.reset();
		for (int y = MIN; y <= MAX; y++) {
			for (int x = MIN; x <= MAX; x++) {
				for (int z = MAX; z >= x; z--) {
					board.makeMove(x, y, PlayerID.O);
				}
			}
			for (int i = MIN; i <= MAX; i++) {
				assertTrue(board.hasWon(i, y, MAX + 1 - i));
			}
		}
		board.reset();
		PlayerID playerID = PlayerID.O;
		for (int x = MIN; x <= MAX; x++) {
			for (int z = MAX; z >= x; z--) {
				board.makeMove(x, MIN, playerID);
				playerID = playerID.other();
			}
		}
		assertFalse(board.hasWon(MIN, MIN, MIN));
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
		board.makeMove(1, 1, PlayerID.O);
		assertFalse(board.isEmptyCell(1, 1, 1));
		assertTrue(board.isEmptyCell(1, 1, 2));
		assertTrue(board.isEmptyCell(1, 1, 3));
		assertTrue(board.isEmptyCell(1, 1, 4));
		board.makeMove(1, 1, PlayerID.O);
		board.makeMove(1, 1, PlayerID.X);
		assertEquals(board.getCellOwner(1, 1, 1), PlayerID.O);
		assertEquals(board.getCellOwner(1, 1, 2), PlayerID.O);
		assertNotEquals(board.getCellOwner(1, 1, 3), PlayerID.O);
		assertEquals(board.getCellOwner(1, 1, 3), PlayerID.X);
	}
	
	@Test
	public void testReset() {
		for (int i = 1; i <= 4; i++) {
			for (int j = 1; j <= 4; j++) {
				for (int k = 1; k <= 4; k++) {
					assertTrue(board.isEmptyCell(i, j, k));
				}
			}
		}
		board.makeMove(1, 2, PlayerID.O);
		board.makeMove(1, 2, PlayerID.X);
		board.makeMove(1, 2, PlayerID.O);	
		board.makeMove(3, 2, PlayerID.X);
		board.makeMove(4, 2, PlayerID.O);
		board.reset();
		for (int i = 1; i <= 4; i++) {
			for (int j = 1; j <= 4; j++) {
				for (int k = 1; k <= 4; k++) {
					assertTrue(board.isEmptyCell(i, j, k));
				}
			}
		}
	}
	
	
}
