package clientserver;

import game.Board;
import game.Disc;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;

/**
 * P2 prac wk4. <br>
 * Client.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class Client extends Thread {
	// PROTOCOL
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
	public static final int FIRST_PLAYER = 0;
	public static final int SECOND_PLAYER = 1;
	// END OF PROTOCOL
	private String clientName;
	private MessageUI mui;
	private Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private boolean loop;
	private boolean isIngame;
	private ArrayList<String> invites;
	private Board board;
	private int currPlayer;

	/**
	 * Constructs a Client-object and tries to make a socket connection
	 */
	public Client(String name, InetAddress host, int port, MessageUI muiArg)
			throws IOException {
		this.clientName = name;
		this.sock = new Socket(host, port);
		this.mui = muiArg;
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.loop = true;
		this.isIngame = false;
		this.invites = new ArrayList<String>();
		System.out.println("Your name is: " + name);
	}

	/**
	 * Reads the messages in the socket connection. Each message will be
	 * forwarded to the MessageUI
	 */

	public void run() {
		sendMessage(CONNECT + " " + getClientName());
		while (loop) {
			try {
				String line = in.readLine();
				mui.addMessage("Server: " + line);
				String[] serverMessage = line.split("\\s+");
				switch (serverMessage[0]) {
				case Server.ACCEPT_CONNECT:
					connect(serverMessage);
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
					error(line);
					break;
				}
			} catch (IOException | NullPointerException e) {
				shutdown();
			}
		}
	}

	private void connect(String[] serverMessage) {
		mui.addMessage("Successfully established connection to server: "
				+ sock.getRemoteSocketAddress().toString() // IP of
															// the
															// server
				+ ":" + sock.getPort()); // Port of the server
		String listOfFeatures = "";
		for (int i = 1; i < serverMessage.length; i++) {
			// TODO: Print dit beter?
			listOfFeatures = listOfFeatures + serverMessage[i] + " ";
		}
		mui.addMessage("The features of this server are: " + listOfFeatures);
		// TODO: Discuss if the lobby should be asked for here.
	}

	private void lobby(String[] serverMessage) {
		mui.addMessage("The people that are currently in the lobby are: ");
		String listOfPeople = "";
		for (int i = 1; i < serverMessage.length; i++) {
			// TODO: Print dit beter?
			listOfPeople = listOfPeople + serverMessage[i] + " ";
		}
		mui.addMessage(listOfPeople);
	}

	private void invite(String[] serverMessage) {
		String opponentName = serverMessage[1];
		invites.add(opponentName);
		if (!isIngame) {
			mui.addMessage("Player: " + opponentName
					+ " has invited you to a game of Connect4!");
		}
	}

	private void gameStart(String[] serverMessage) {
		mui.addMessage("A game between you and " + serverMessage[2]
				+ " has started!");
		this.isIngame = true;
		currPlayer = -1; // Not set yet.
		// DEFINITION: currPlayer == 0 > Disc.YELLOW, currPlayer ==
		// 1 > Disc.RED
		board = new Board();
	}

	private void gameEnd(String[] serverMessage) {
		this.isIngame = false;
		// TODO: Maybe add something here? IDKLOL.
	}

	private void requestMove(String[] serverMessage) {
		if (currPlayer == -1) {
			currPlayer = FIRST_PLAYER;
		}
	}

	private void moveOK(String[] serverMessage) {
		if (currPlayer == -1) {
			currPlayer = SECOND_PLAYER;
		}
		int move = -1;
		// TODO: if else?
		switch (currPlayer) {
		case FIRST_PLAYER:
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			board.insertDisc(move, Disc.YELLOW);
			break;
		case SECOND_PLAYER:
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("Server did not send a valid move. TERMINATING.");
				shutdown();
			}
			board.insertDisc(move, Disc.RED);
			break;
		}
	}

	private void error(String line) {
		mui.addMessage(line);
	}

	// TODO: Request a move from the player.
	/** send a message to a ClientHandler. */
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	/** close the socket connection. */
	public void shutdown() {
		loop = false;
		isIngame = false;
		try {
			sock.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		System.exit(0);
	}

	/** returns the client name */
	public String getClientName() {
		return clientName;
	}

} // end of class Client
