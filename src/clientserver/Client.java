package clientserver;

import game.Board;
import game.Disc;
import game.HumanPlayer;
import game.Player;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.HashMap;
import java.util.Map;

/**
 * Client program for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Client {
	// The protocol, as discussed in our TI-2 group. For further explanation,
	// you can look at the protocol documentation.
	public static final String CONNECT = "CONNECT";
	public static final String QUIT = "QUIT";
	public static final String INVITE = "INVITE";
	public static final String ACCEPT_INVITE = "ACCEPT";
	public static final String DECLINE_INVITE = "DECLINE";
	public static final String MOVE = "MOVE";
	public static final String CHAT = "CHAT";
	public static final String REQUEST_BOARD = "REQUEST";
	public static final String REQUEST_LOBBY = "LOBBY";
	public static final String REQUEST_LEADERBOARD = "LEADERBOARD";
	public String firstPlayer;
	public String secondPlayer;
	// END OF PROTOCOL

	/**
	 * The name of this Client.
	 */
	private String clientName;

	/**
	 * The User Interface of this Client.
	 */
	private ClientTUI mui;
	/**
	 * The Socket of this Client.
	 */
	private Socket sock;
	/**
	 * The BufferedReader that will be used to communicate over the Socket.
	 */
	private BufferedReader in;
	/**
	 * The BufferedWriter that will be used to communicate over the Socket.
	 */
	private BufferedWriter out;
	/**
	 * While this boolean is true, it makes sure that commands are continuously
	 * read from the BufferedReader.
	 */
	private boolean loop;
	/**
	 * A variable to test if a Player is in-game. If they are, they won't
	 * receive any invite messages.
	 */
	private boolean isIngame;
	/**
	 * The Board this Client uses for determining their move.
	 */
	private Board board;
	/**
	 * An integer to determine which Player's turn it is.
	 */
	private String currPlayer;
	/**
	 * A boolean to determine whether this Client is connected.
	 */
	private boolean isConnected;
	/**
	 * The Player this Client is.
	 */
	private Player localPlayer;
	/**
	 * If the Client requests the Board from the server, it's saved here that it
	 * has already been requested, so it's not requested for a second time.
	 */
	private boolean requestedBoard;
	/**
	 * A Map of invites this Client is invited by. This map gets emptied every
	 * time a Game starts.
	 */
	private Map<String, Integer[]> invitedBy;
	/**
	 * A Map of invited this Client sent. This map gets emptied every time a
	 * Game starts.
	 */
	private Map<String, Integer[]> invited;

	/*@	private invariant sock != null;
	 	private invariant mui != null;
	 	private invariant in != null;
	 	private invariant out != null;
	  	private invariant invited != null;
	  	private invariant invitedBy != null;
	  	private invariant localPlayer != null;
	 */

	/**
	 * Constructs a Client object and tries to make a Socket connection
	 * 
	 * @param host
	 *            The IP-adress of this Client
	 * @param port
	 *            The port of this Client
	 * @param muiArg
	 *            The MessageUI for this Client
	 * @param localPlayer
	 *            The Player Object to use for this Client
	 */
	/*@ requires host != null;
	 	requires port >= 1 & port <= 65535;
	 	requires muiArg != null;
	 	requires localPlayer != null;
	 */
	public Client(InetAddress host, int port, ClientTUI muiArg,
			Player localPlayer) throws IOException {
		this.sock = new Socket(host, port);
		this.mui = muiArg;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.loop = true;
		this.isIngame = false;
		this.invitedBy = new HashMap<String, Integer[]>();
		this.isConnected = false;
		this.localPlayer = localPlayer;
		this.requestedBoard = false;
		this.invited = new HashMap<String, Integer[]>();
	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command by calling the method created
	 * for it.
	 */
	public void readInput() {
		while (loop) {
			String line = "";
			try {
				line = in.readLine();
			} catch (IOException | NullPointerException e) {
				shutdown();
			}
			mui.addMessage("Server: " + line);
			String[] serverMessage = line.split("\\s+");
			switch (serverMessage[0]) {
			case Server.ACCEPT_CONNECT:
				isConnected = true;
				connect(serverMessage);
				mui.start();
				break;
			case Server.LOBBY:
				lobby(serverMessage);
				break;
			case Server.INVITE:
				invite(serverMessage);
				break;
			case Server.GAME_START:
				gameStart(serverMessage);
				break;
			case Server.GAME_END:
				gameEnd(serverMessage);
				break;
			case Server.REQUEST_MOVE:
				requestMove(serverMessage);
				break;
			case Server.MOVE_OK:
				moveOK(serverMessage);
				break;
			case Server.ERROR:
				mui.addMessage(line);
				if (!isConnected) {
					mui.askName();
				}
				break;
			case Server.BOARD:
				board = toBoard(line);
				notifyAll();
			}

		}
	}

	/**
	 * This method accepts the Server.CONNECT packet sent by the Server. When
	 * this method is called, it prints that a connection has been established
	 * with the Server, as well as the IP adress and port of the Server. After
	 * this, it lists the features the Server has.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@	requires serverMessage[0].equals(Server.ACCEPT_CONNECT);
	private void connect(String[] serverMessage) {
		mui.addMessage("Successfully established connection to server: "
		// IP of the server
				+ sock.getRemoteSocketAddress().toString());
		mui.addMessage("The features of this server are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.LOBBY packet sent by the Server. When this
	 * method is called, it shows the Client the other Clients that are
	 * currently in the lobby.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.LOBBY);
	private void lobby(String[] serverMessage) {
		mui.addMessage("The people that are currently in the lobby are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.INVITE packet sent by the Server. When
	 * this method is called, it adds the inviter (and to an inviterlist, and
	 * potentially, the custom board size. If the player isn't ingame, it will
	 * also show the Client that they have been invited by that Client.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.INVITE);
	private void invite(String[] serverMessage) {
		String opponentName = serverMessage[1];
		if (serverMessage.length == 2) {
			addServerInvite(opponentName);
			if (!isIngame) {
				mui.addMessage("Player: "
						+ opponentName
						+ " has invited you to a game of Connect4 (default boardsize)!");
			}
		} else if (serverMessage.length >= 4) {
			try {
				addServerInvite(opponentName,
						Integer.parseInt(serverMessage[2]),
						Integer.parseInt(serverMessage[3]));
			} catch (NumberFormatException e) {
				mui.addMessage("The server just sent an invite with an invalid custom board size.");
			}
		}
	}

	/**
	 * This method accepts the Server.GAME_START packet sent by the Server. When
	 * this method is called, it will show the Client that a the game is
	 * started. The Client is set to being in-game, and a new Board is created.
	 * The size of the Board is dependant on the size sent in the invite (the
	 * Boardsizes of the invites are saved in a HashMap).
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@ requires serverMessage[0].equals(Server.GAME_START);
	 	ensures board != null;
	 	ensures this.isIngame;
	 	ensures currPlayer == null;
	 */
	private void gameStart(String[] serverMessage) {
		firstPlayer = serverMessage[1];
		secondPlayer = serverMessage[2];

		if (firstPlayer.equals(getClientName())) {
			mui.addMessage("A game between you and " + secondPlayer
					+ " has started!");
			Integer[] boardSize = invitedBy.get(secondPlayer);
			if (boardSize != null) {
				board = new Board(boardSize[1], boardSize[0]);
			} else {
				mui.addMessage("Using default boardsize.");
				board = new Board();
			}
		} else {
			mui.addMessage("A game between you and " + firstPlayer
					+ " has started!");
			Integer[] boardSize = invited.get(firstPlayer);
			if (boardSize != null) {
				board = new Board(boardSize[0], boardSize[1]);
			} else {
				mui.addMessage("Using default boardsize.");
				board = new Board();
			}
		}

		this.isIngame = true;
		currPlayer = null; // Not set yet.
		// DEFINITION: currPlayer == 0 > Disc.YELLOW, currPlayer ==
		// 1 > Disc.RED

		invitedBy.clear();
		invited.clear();
		mui.addMessage(board.toString());
		mui.addMessage("You are YELLOW");
	}

	/**
	 * This method accepts the Server.GAME_END packet sent by the Server. When
	 * this method is called, it will set the Client to no longer being in-game.
	 * It will also show the client who won the game, or if the game was a draw.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@	requires serverMessage[0].equals(Server.GAME_END);
	 	ensures !this.isIngame;
	 */
	private void gameEnd(String[] serverMessage) {
		this.isIngame = false;
		if (serverMessage.length > 2) {
			mui.addMessage("The winner is: " + serverMessage[2]);
		} else if (serverMessage.length == 2) {
			if (serverMessage[1].equals(Game.DRAW)) {
				mui.addMessage("The game was a draw!");
			} else {
				mui.addMessage(serverMessage.toString());
			}
		}
	}

	/**
	 * This method accepts the Server.MOVE packet sent by the Server. When this
	 * method is called, it will request a move from the Player. If the Player
	 * is a HumanPlayer, the GameView will be used to ask for a move. If the
	 * Player is a ComputerPlayer, the determineMove() method from the
	 * ComputerPlayer is used instead.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.REQUEST_MOVE);
	private void requestMove(String[] serverMessage) {
		if (currPlayer == null) {
			currPlayer = firstPlayer;
		}
		if (localPlayer instanceof HumanPlayer) {
			localPlayer.determineMove(board);
		} else {
			int move = localPlayer.determineMove(board);
			sendMessage(MOVE + " " + move);
		}
	}

	/**
	 * This method accepts the Server.MOVE_OK packet sent by the Server. When
	 * this method is called, it will update the Board by inserting the Disc for
	 * the Player that was given in the packet. If it can't insert the Disc, it
	 * will request the Board and try to insert the Disc once again.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.MOVE_OK);
	private synchronized void moveOK(String[] serverMessage) {
		if (currPlayer == null) {
			currPlayer = secondPlayer;
		}
		int move = -1;
		if (currPlayer.equals(firstPlayer)) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.YELLOW);
				currPlayer = secondPlayer;
			} else {
				if (!requestedBoard) {
					requestBoard();
					requestedBoard = true;
					try {
						wait();
						mui.addMessage("This is the board the server has: ");
						mui.addMessage(board.toString());
						moveOK(serverMessage);
					} catch (InterruptedException e) {
						mui.addMessage("Interrupted.");
						shutdown();
					}
				} else {
					mui.addMessage("Can't make the move on both the local board, and the board on the server. TERMINATING.");
					shutdown();
				}
			}

		} else if (currPlayer.equals(secondPlayer)) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.RED);
				currPlayer = firstPlayer;
			} else {
				if (!requestedBoard) {
					requestBoard();
					requestedBoard = true;
					try {
						wait();
						moveOK(serverMessage);
					} catch (InterruptedException e) {
						mui.addMessage("Interrupted.");
						shutdown();
					}
				} else {
					mui.addMessage("Can't make the move on both the local board, and the board on the server. TERMINATING.");
					shutdown();
				}

				mui.addMessage("Server sent an invalid move. TERMINATING.");
			}
		}
		mui.addMessage(board.toString());
	}

	/**
	 * This method sends a message to the ClientHandler using the OutputStream
	 * out.
	 * 
	 * @param msg
	 *            The message to be sent.
	 */
	//@ requires msg != null;
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/**
	 * This method closes the Socket connection and exits the program. On a side
	 * note, before it does this, it also sets the loop and isIngame variables
	 * for this Client to false.
	 */
	public void shutdown() {
		loop = false;
		isIngame = false;
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * This method returns the name of this Client.
	 */
	/*@ pure */public String getClientName() {
		return clientName;
	}

	/**
	 * This method sets the name for this Client.
	 * 
	 * @param name
	 *            The name this Client should have.
	 */
	//@ ensures getClientName().equals(name);
	public void setClientName(String name) {
		clientName = name;
	}

	/**
	 * This method makes a Board out of the packet the server sends when the
	 * Board is requested.
	 * 
	 * @param line
	 *            The Boardpacket the Server sent.
	 * @return A new Board object with the Board as sent by the Server.
	 */
	//@ requires line != null;
	public Board toBoard(String line) {
		String[] protocol = line.split(" ");
		Board test = null;
		try {
			int boardColumns = Integer.parseInt(protocol[1]);
			int boardRows = Integer.parseInt(protocol[2]);

			test = new Board(boardRows, boardColumns);
			int i = 3;
			for (int row = boardRows - 1; row >= 0; row--) {
				for (int col = 0; col < boardColumns; col++) {
					if (Integer.parseInt(protocol[i]) == 0) {
						//Disc.EMPTY
						test.setField(row, col, Disc.EMPTY);
					} else if (Integer.parseInt(protocol[i]) == 1) {
						//Disc.YELLOW
						test.setField(row, col, Disc.YELLOW);
					} else if (Integer.parseInt(protocol[i]) == 2) {
						//Disc.RED
						test.setField(row, col, Disc.RED);
					}
					i++;
				}
			}

		} catch (NumberFormatException e) {
			mui.addMessage("Server sent a wrong board. TERMINATING.");
			shutdown();
		}
		return test;
	}

	/**
	 * This method is used to convert an Stringarray to a single String.
	 * 
	 * @param array
	 *            The array to convert.
	 * @return The array converted to one line.
	 */
	//@ requires array != null;
	public String arrayToLine(String[] array) {
		String retLine = "";
		for (int i = 1; i < array.length; i++) {
			retLine += " " + array[i];
		}
		return retLine;
	}

	/**
	 * Method to request the board from the server.
	 */
	private void requestBoard() {
		sendMessage(REQUEST_BOARD);
	}

	/**
	 * Method to add an invite to the list of people this Client has invited.
	 * 
	 * @param name
	 *            The name this Client just invited.
	 */
	public void addClientInvite(String name) {
		addClientInvite(name, 6, 7);
	}

	/**
	 * Method to add an invite to the list of people this Client has invited
	 * with a custom Board size.
	 * 
	 * @param name
	 *            The name this Client just invited.
	 * @param BoardX
	 *            The custom Board size's X value.
	 * @param BoardY
	 *            The custom Board size's Y value.
	 */
	public void addClientInvite(String name, int BoardX, int BoardY) {
		invited.put(name, new Integer[] { BoardX, BoardY });
	}

	/**
	 * Method to add an invite to the list of people this Client has been
	 * invited by.
	 * 
	 * @param name
	 *            The name this Client just got invited by.
	 */
	public void addServerInvite(String name) {
		addServerInvite(name, 6, 7);
	}

	/**
	 * Method to add an invite to the list of people this Client has been
	 * invited by with a custom Board size.
	 * 
	 * @param name
	 *            The name this Client just got invited by.
	 * @param BoardX
	 *            The custom Board size's X value.
	 * @param BoardY
	 *            The custom Board size's Y value.
	 */
	public void addServerInvite(String name, int BoardX, int BoardY) {
		invitedBy.put(name, new Integer[] { BoardX, BoardY });
	}
}
